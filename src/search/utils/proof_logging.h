#ifndef UTILS_PROOF_LOGGING_H
#define UTILS_PROOF_LOGGING_H

#include "../state_id.h"
#include "../task_proxy.h"

#include <string>

namespace utils {

class ProofLog{
    std::string file_name;

public:
    explicit ProofLog(const std::string &file_name);

    void append_to_proof_log(const std::string& line);
    void add_state_reification(StateID id, State s);
};

}

#endif