#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <sys/ipc.h>
#include <sys/shm.h>
#include <sys/msg.h>
#include <pthread.h>
#include <limits.h>
#include <math.h>
#include <time.h>

// ==========================================
// 1. DEFINITIONS & STRUCTS (From PDF)
// ==========================================

#define MAX_TRUCKS 250
#define TRUCK_MAX_CAP 20
#define MAX_NEW_REQUESTS 50
#define MAX_TOTAL_PACKAGES 5000
#define ALPHABET_SIZE 4

// Strategy Constants
#define MAX_CARRY_LIMIT 6 // Limit carried packages to keep Auth String guessable (4^6 = 4096 ops)

char MOVES[] = {'u', 'd', 'l', 'r'};

typedef struct PackageRequest {
    int packageId;
    int pickup_x;
    int pickup_y;
    int dropoff_x;
    int dropoff_y;
    int arrival_turn;
    int expiry_turn;
} PackageRequest;

typedef struct MainSharedMemory {
    char authStrings[MAX_TRUCKS][TRUCK_MAX_CAP + 1];
    char truckMovementInstructions[MAX_TRUCKS];
    int pickUpCommands[MAX_TRUCKS];
    int dropOffCommands[MAX_TRUCKS];
    int truckPositions[MAX_TRUCKS][2];
    int truckPackageCount[MAX_TRUCKS];
    int truckTurnsInToll[MAX_TRUCKS];
    PackageRequest newPackageRequests[MAX_NEW_REQUESTS];
    int packageLocations[MAX_TOTAL_PACKAGES][2];
} MainSharedMemory;

typedef struct TurnChangeResponse {
    long mtype;
    int turnNumber;
    int newPackageRequestCount;
    int errorOccured;
    int finished;
} TurnChangeResponse;

typedef struct TurnReadyRequest {
    long mtype;
} TurnReadyRequest;

typedef struct SolverRequest {
    long mtype;
    int truckNumber;
    char authStringGuess[TRUCK_MAX_CAP + 1];
} SolverRequest;

typedef struct SolverResponse {
    long mtype;
    int guessIsCorrect;
} SolverResponse;

// Local State Structs
typedef struct {
    int id;
    int px, py, dx, dy;
    int expiry;
    int status; // 0: New, 1: Assigned, 2: Picked, 3: Delivered
    int carrier_id;
} Package;

typedef struct {
    int id;
    int target_pkg_idx; // -1 if idle
    int action_type;    // 0: idle, 1: pickup, 2: dropoff
    int assigned_packages[TRUCK_MAX_CAP]; // IDs of packages currently on board
    int count;
} TruckState;

// Global Variables
int N, D, S, T, B;
key_t shm_key, mq_key;
int shm_id, mq_id;
MainSharedMemory *shm;
int *solver_qids;
pthread_mutex_t *solver_locks; // Mutex for each solver

Package all_packages[MAX_TOTAL_PACKAGES];
int total_pkg_count = 0;
TruckState truck_states[MAX_TRUCKS];
int toll_map[500][500]; // Local map of discovered tolls

// ==========================================
// 2. SOLVER LOGIC (Brute Force with Threads)
// ==========================================

typedef struct {
    int truck_id;
    int length;
    int solver_idx;
} ThreadArgs;

// Recursive Brute Force Function
int try_guess(int qid, int truck_id, char* current_str, int len, int depth) {
    if (depth == len) {
        SolverRequest req;
        SolverResponse resp;
        
        req.mtype = 3;
        req.truckNumber = -1; // Ignored by solver for mtype 3
        strcpy(req.authStringGuess, current_str);
        
        if (msgsnd(qid, &req, sizeof(SolverRequest) - sizeof(long), 0) == -1) return 0;
        if (msgrcv(qid, &resp, sizeof(SolverResponse) - sizeof(long), 4, 0) == -1) return 0;
        
        return resp.guessIsCorrect;
    }

    for (int i = 0; i < 4; i++) {
        current_str[depth] = MOVES[i];
        current_str[depth + 1] = '\0';
        if (try_guess(qid, truck_id, current_str, len, depth + 1)) {
            return 1;
        }
    }
    return 0;
}

void* solve_auth_string(void* args) {
    ThreadArgs* data = (ThreadArgs*)args;
    int tid = data->truck_id;
    int len = data->length;
    int s_idx = data->solver_idx;
    int qid = solver_qids[s_idx];

    // Lock this solver so no other thread interlaces messages
    pthread_mutex_lock(&solver_locks[s_idx]);

    // 1. Set Target Truck (mtype 2)
    SolverRequest req;
    req.mtype = 2;
    req.truckNumber = tid;
    msgsnd(qid, &req, sizeof(SolverRequest) - sizeof(long), 0);

    // 2. Brute Force (mtype 3 & 4)
    char guess_buf[TRUCK_MAX_CAP + 1];
    memset(guess_buf, 0, sizeof(guess_buf));
    
    int found = try_guess(qid, tid, guess_buf, len, 0);

    if (found) {
        strcpy(shm->authStrings[tid], guess_buf);
    } else {
        // Should not happen given the logic, but fail safe
        shm->authStrings[tid][0] = '\0'; 
    }

    pthread_mutex_unlock(&solver_locks[s_idx]);
    free(data);
    return NULL;
}

// ==========================================
// 3. HELPER FUNCTIONS
// ==========================================

int dist(int x1, int y1, int x2, int y2) {
    return abs(x1 - x2) + abs(y1 - y2);
}

void parse_input() {
    FILE *f = fopen("input.txt", "r");
    if (!f) exit(1);
    fscanf(f, "%d %d %d %d %d %d %d", &N, &D, &S, &T, &B, &shm_key, &mq_key);
    
    solver_qids = malloc(sizeof(int) * S);
    solver_locks = malloc(sizeof(pthread_mutex_t) * S);
    
    for (int i = 0; i < S; i++) {
        key_t skey;
        fscanf(f, "%d", &skey);
        solver_qids[i] = msgget(skey, 0666);
        pthread_mutex_init(&solver_locks[i], NULL);
    }
    fclose(f);
}

void init_ipc() {
    shm_id = shmget(shm_key, sizeof(MainSharedMemory), 0666);
    shm = (MainSharedMemory*)shmat(shm_id, NULL, 0);
    mq_id = msgget(mq_key, 0666);
    
    // Initialize local state
    memset(toll_map, 0, sizeof(toll_map));
    for(int i=0; i<MAX_TRUCKS; i++) {
        truck_states[i].id = i;
        truck_states[i].target_pkg_idx = -1;
        truck_states[i].count = 0;
    }
}

// ==========================================
// 4. MAIN LOGIC LOOP
// ==========================================

int main() {
    parse_input();
    init_ipc();

    // Handshake Loop
    TurnChangeResponse turn_resp;
    TurnReadyRequest turn_req;
    turn_req.mtype = 1;

    // Initial Wait
    msgrcv(mq_id, &turn_resp, sizeof(TurnChangeResponse) - sizeof(long), 2, 0);

    while (!turn_resp.finished) {
        int current_turn = turn_resp.turnNumber;

        // 1. Update Packages
        for (int i = 0; i < turn_resp.newPackageRequestCount; i++) {
            PackageRequest *req = &shm->newPackageRequests[i];
            all_packages[total_pkg_count].id = req->packageId;
            all_packages[total_pkg_count].px = req->pickup_x;
            all_packages[total_pkg_count].py = req->pickup_y;
            all_packages[total_pkg_count].dx = req->dropoff_x;
            all_packages[total_pkg_count].dy = req->dropoff_y;
            all_packages[total_pkg_count].expiry = req->expiry_turn;
            all_packages[total_pkg_count].status = 0; // New
            total_pkg_count++;
        }

        // 2. Update Toll Map & Reset SHM Commands
        for (int i = 0; i < D; i++) {
            if (shm->truckTurnsInToll[i] > 0) {
                toll_map[shm->truckPositions[i][0]][shm->truckPositions[i][1]] = 1;
            }
            shm->truckMovementInstructions[i] = 's';
            shm->pickUpCommands[i] = -1;
            shm->dropOffCommands[i] = -1;
            shm->authStrings[i][0] = '\0';
        }

        // 3. Assign Packages (Strategy: Expired First, Close Distance Second)
        for (int i = 0; i < D; i++) {
            // Skip if stuck in toll
            if (shm->truckTurnsInToll[i] > 0) continue;

            int tx = shm->truckPositions[i][0];
            int ty = shm->truckPositions[i][1];

            // A. Check for Dropoffs first
            int dropped = 0;
            for (int k = 0; k < truck_states[i].count; k++) {
                int pid = truck_states[i].assigned_packages[k];
                // Find pkg in global array
                int p_idx = -1;
                for(int p=0; p<total_pkg_count; p++) if(all_packages[p].id == pid) p_idx = p;
                
                if (p_idx != -1 && tx == all_packages[p_idx].dx && ty == all_packages[p_idx].dy) {
                    shm->dropOffCommands[i] = pid;
                    all_packages[p_idx].status = 3; // Delivered
                    
                    // Remove from local state
                    for(int m=k; m<truck_states[i].count-1; m++) 
                        truck_states[i].assigned_packages[m] = truck_states[i].assigned_packages[m+1];
                    truck_states[i].count--;
                    dropped = 1;
                    break; // Only 1 drop per turn
                }
            }
            if (dropped) continue; // Cannot move if dropping

            // B. Check for Pickups
            int picked = 0;
            // Check if we are at a target pickup location
            if (truck_states[i].target_pkg_idx != -1 && truck_states[i].count < MAX_CARRY_LIMIT) {
                int p_idx = truck_states[i].target_pkg_idx;
                if (all_packages[p_idx].status == 1 && // Assigned
                    tx == all_packages[p_idx].px && ty == all_packages[p_idx].py) {
                    
                    shm->pickUpCommands[i] = all_packages[p_idx].id;
                    truck_states[i].assigned_packages[truck_states[i].count++] = all_packages[p_idx].id;
                    all_packages[p_idx].status = 2; // Picked
                    all_packages[p_idx].carrier_id = i;
                    truck_states[i].target_pkg_idx = -1; // Request satisfied
                    picked = 1;
                }
            }
            if (picked) continue; // Cannot move if picking

            // C. Assign New Target if Idle
            if (truck_states[i].target_pkg_idx == -1 && truck_states[i].count < MAX_CARRY_LIMIT) {
                int best_idx = -1;
                double best_score = 1e9;

                for (int p = 0; p < total_pkg_count; p++) {
                    if (all_packages[p].status == 0) { // Unassigned
                        int d = dist(tx, ty, all_packages[p].px, all_packages[p].py);
                        // Score: Expiry is priority, Distance is secondary cost
                        // Lower score is better
                        double score = (all_packages[p].expiry - current_turn) * 10.0 + d;
                        
                        if (score < best_score) {
                            best_score = score;
                            best_idx = p;
                        }
                    }
                }
                
                if (best_idx != -1) {
                    truck_states[i].target_pkg_idx = best_idx;
                    all_packages[best_idx].status = 1; // Assigned
                }
            }

            // D. Determine Movement
            int target_x = tx, target_y = ty;
            
            // If carrying, go to dropoff of the first package (FIFO drop logic for simplicity)
            if (truck_states[i].count > 0) {
                int pid = truck_states[i].assigned_packages[0];
                for(int p=0; p<total_pkg_count; p++) {
                    if(all_packages[p].id == pid) {
                        target_x = all_packages[p].dx;
                        target_y = all_packages[p].dy;
                        break;
                    }
                }
            } 
            // If empty and assigned, go to pickup
            else if (truck_states[i].target_pkg_idx != -1) {
                target_x = all_packages[truck_states[i].target_pkg_idx].px;
                target_y = all_packages[truck_states[i].target_pkg_idx].py;
            }

            // Greedy Move
            char move = 's';
            if (target_x > tx) move = 'r';
            else if (target_x < tx) move = 'l';
            else if (target_y > ty) move = 'd';
            else if (target_y < ty) move = 'u';

            // Avoid immediate toll collision if possible (Simple 1-step lookahead)
            int nx = tx, ny = ty;
            if (move == 'r') nx++; else if (move == 'l') nx--; 
            else if (move == 'd') ny++; else if (move == 'u') ny--;
            
            if (toll_map[nx][ny]) {
                // Try alternative perpendicular move
                if (move == 'r' || move == 'l') {
                   if (target_y > ty) move = 'd'; else move = 'u';
                } else {
                   if (target_x > tx) move = 'r'; else move = 'l';
                }
            }

            shm->truckMovementInstructions[i] = move;
        }

        // 4. Solve Auth Strings (Parallelized)
        pthread_t threads[MAX_TRUCKS];
        int thread_count = 0;

        for (int i = 0; i < D; i++) {
            // Only need auth if carrying packages AND moving
            if (truck_states[i].count > 0 && shm->truckMovementInstructions[i] != 's') {
                ThreadArgs* args = malloc(sizeof(ThreadArgs));
                args->truck_id = i;
                args->length = truck_states[i].count;
                // Simple Round Robin load balancing for solvers
                args->solver_idx = thread_count % S; 
                
                pthread_create(&threads[thread_count], NULL, solve_auth_string, args);
                thread_count++;
            }
        }

        // Join all solver threads
        for (int i = 0; i < thread_count; i++) {
            pthread_join(threads[i], NULL);
        }

        // 5. Submit Turn
        msgsnd(mq_id, &turn_req, sizeof(TurnReadyRequest) - sizeof(long), 0);
        
        // Wait for next
        msgrcv(mq_id, &turn_resp, sizeof(TurnChangeResponse) - sizeof(long), 2, 0);
    }

    // Cleanup
    shmdt(shm);
    free(solver_qids);
    free(solver_locks);
    return 0;
}
