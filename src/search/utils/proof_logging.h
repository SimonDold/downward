#ifndef UTILS_PROOF_LOGGING_H
#define UTILS_PROOF_LOGGING_H

//include "../search_space.h"

#include <optional>
#include <string>

//class SearchNode;
//class OperatorID;

namespace utils {

enum class ProofPart {
    REIFICATION,
    DERIVATION
};

class ProofLog{

public:
    explicit ProofLog();

    void append_to_proof_log(const std::string& line, ProofPart proof_part);
    void op_implies_min_cost_delta(int op_id);
    void reify_min_cost_delta(int min_cost);
};

}

#endif