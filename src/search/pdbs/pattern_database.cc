#include "pattern_database.h"

#include "../task_utils/task_properties.h"

#include "../utils/logging.h"
#include "../utils/math.h"

#include <cassert>
#include <iostream>
#include <limits>
#include <vector>

using namespace std;

namespace pdbs {
Projection::Projection(
    const TaskProxy &task_proxy, const Pattern &pattern)
    : pattern(pattern) {
    task_properties::verify_no_axioms(task_proxy);
    task_properties::verify_no_conditional_effects(task_proxy);
    assert(utils::is_sorted_unique(pattern));

    domain_sizes.reserve(pattern.size());
    hash_multipliers.reserve(pattern.size());
    num_abstract_states = 1;
    for (int pattern_var_id : pattern) {
        hash_multipliers.push_back(num_abstract_states);
        VariableProxy var = task_proxy.get_variables()[pattern_var_id];
        int domain_size = var.get_domain_size();
        domain_sizes.push_back(domain_size);
        if (utils::is_product_within_limit(
                num_abstract_states,
                domain_size,
                numeric_limits<int>::max())) {
            num_abstract_states *= domain_size;
        } else {
            cerr << "Given pattern is too large! (Overflow occured): " << endl;
            cerr << pattern << endl;
            utils::exit_with(utils::ExitCode::SEARCH_CRITICAL_ERROR);
        }
    }
}

int Projection::rank(const vector<int> &state) const {
    size_t index = 0;
    for (size_t i = 0; i < pattern.size(); ++i) {
        index += hash_multipliers[i] * state[pattern[i]];
    }
    return index;
}

int Projection::unrank(int state_index, int var) const {
    assert(hash_multipliers.size()>var);
    assert(hash_multipliers[var]>0);
    int temp = state_index / hash_multipliers[var];
    return temp % domain_sizes[var];
}

string get_name_aux(Pattern pattern){
    ostringstream name;
    name << "{";
    for (auto & var : pattern) {
        name << var << "_";
    }
    name << "}";
    return name.str();
}

string Projection::get_name() const {
    return get_name_aux(pattern);
}

string Projection::abstract_state(int state_index) const {
    ostringstream name;
    name << "a_" << get_name() << "[s[" << state_index << "]]";
    return name.str();
}

void Projection::bireif_abstract_state(int state_index) const{
    for (int i=0; i<=1; ++i) {

        ostringstream reif_var;
        reif_var << abstract_state(state_index) << (i ? ":" : ".");
        vector<string> conjuncts(pattern.size());
        for (int var_position = 0; var_position < pattern.size(); ++var_position) {
            ostringstream conjunct;
            conjunct << "var_" << pattern[var_position] << "_" << unrank(state_index, var_position) << (i ? ":" : ".");
            conjuncts[var_position] = conjunct.str();
        }
        utils::ProofLog::bireif_conjunction(reif_var.str(), conjuncts, "");
    }
}

void Projection::bireif_abstract_state_with_balance(int state_index, int balance) const {
    ostringstream name;
    name << "node[a_" << get_name() << "[s[" << state_index << "]],balance_geq_" << balance << "]";
    for (int i=0; i<=1; ++i) {
        utils::ProofLog::bireif_balance_leq(balance-1);
        ostringstream reif_var, conjunct_1, conjunct_2;
        reif_var << name.str() << (i ? ":" : ".");
        conjunct_1 << "a_" << get_name() << "[s[" << state_index << "]]" << (i ? ":" : ".");
        conjunct_2 << "balance_geq_" << balance << (i ? ":" : ".");
        utils::ProofLog::bireif_conjunction(reif_var.str(), {conjunct_1.str(), conjunct_2.str()}, "");

    }
}

PatternDatabase::PatternDatabase(
    Projection &&projection,
    vector<int> &&distances)
    : projection(move(projection)),
      distances(move(distances)) {
}

int PatternDatabase::get_value(const vector<int> &state) const {
    int result = distances[projection.rank(state)];
    if (result <= utils::ProofLog::get_proof_log_maxint()){
        projection.bireif_abstract_state_with_balance(projection.rank(state), result);
    }
    return result;
}

double PatternDatabase::compute_mean_finite_h() const {
    double sum = 0;
    int size = 0;
    for (size_t i = 0; i < distances.size(); ++i) {
        if (distances[i] != numeric_limits<int>::max()) {
            sum += distances[i];
            ++size;
        }
    }
    if (size == 0) { // All states are dead ends.
        return numeric_limits<double>::infinity();
    } else {
        return sum / size;
    }
}
}
