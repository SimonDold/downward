#ifndef UTILS_PROOF_LOGGING_H
#define UTILS_PROOF_LOGGING_H

#include <sstream>
#include <string>
#include <vector>

// TODOprooflog remove global variables
extern int proof_log_var_count;
extern int proof_log_max_cost_bits;
namespace utils {

enum class ProofPart {
    REIFICATION,
    DERIVATION,
    INVARIANT
};

int ceil_log_2(int x);

class ProofLog{

public:
    explicit ProofLog() = delete;
    static void append_to_proof_log(const std::string& line, ProofPart proof_part);
    static void append_comment_to_proof_log(const std::string& comment);
    static void append_to_proof_file(const std::string& line, const std::string& file);
    static void append_to_invariant_right(const std::string& summand);
    static void append_to_invariant_left(const std::string& summand);
    static void append_to_invariant_prime_right(const std::string& summand);
    static void append_to_invariant_prime_left(const std::string& summand);
    static void add_spent_geq_x_bireification(const int x);
    static void add_balance_leq_x_bireification(const int x);
    static void bireif_balance_leq(int return_value);
    static void bireif_conjunction(std::string reif_var, std::vector<std::string> conjuncts, std::string comment);
    static void bireif_disjunction(std::string reif_var, std::vector<std::string> disjuncts, std::string comment);
    static void append_files_to_proof_log(std::vector<std::string> files, ProofPart proof_part);
    static void finalize_lemmas(int optimal_cost);
    static int get_proof_log_bits();
    static int get_proof_log_maxint();
    static std::string strips_name_to_veripb_name(const std::string& strips_name);
    static void merge_proof_log_files();
    static bool is_meta_file(std::string meta_file_name);
    static void merge_proof_log_files(std::string meta_file_name);
    static std::vector<std::string> get_subfiles(std::string meta_file_name);
    static void make_proof_file(std::string name);
    static void create_plan_pbp();
    static void finalize_plan_pbp();
    static void append_to_plan_pbp(std::string file_name);
    static int runCommand(const std::string& command);
};

}

#endif
