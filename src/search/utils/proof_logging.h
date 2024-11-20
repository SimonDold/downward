#ifndef UTILS_PROOF_LOGGING_H
#define UTILS_PROOF_LOGGING_H

#include <sstream>
#include <string>

namespace utils {

enum class ProofPart {
    REIFICATION,
    DERIVATION,
    INVARIANT
};

class ProofLog{

public:
    explicit ProofLog() = delete;
    static void append_to_proof_log(const std::string& line, ProofPart proof_part);
    static std::string strips_name_to_veripb_name(const std::string& strips_name);
};

}

#endif