#ifndef UTILS_PROOF_LOGGING_H
#define UTILS_PROOF_LOGGING_H

#include "../search_space.h"

#include <optional>
#include <string>

namespace utils {

enum class ProofPart {
    REIFICATION,
    DERIVATION
};

class ProofLog{
    const std::string reifications_file_name;
    const std::string derivations_file_name;

public:
    explicit ProofLog(const std::string &reifications_file_name,
        const std::string &derivations_file_name);

    void append_to_proof_log(const std::string& line, ProofPart proof_part);
    void add_node_reification(std::optional<SearchNode> node = std::nullopt);
    void add_node_action_invariant(OperatorID op_id, std::optional<SearchNode> node = std::nullopt);
    void op_implies_min_cost_delta(int op_id);
    void reify_min_cost_delta(int min_cost);
};

}

#endif