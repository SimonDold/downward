#ifndef UTILS_PROOF_LOGGING_H
#define UTILS_PROOF_LOGGING_H

#include "../state_id.h"
#include "../task_proxy.h"

#include <string>

namespace utils {
    void appendLineToFile(std::string file_name, std::string line);

    void add_state_reification(StateID id, State s);
}

#endif