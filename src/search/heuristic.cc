#include "heuristic.h"

#include "evaluation_context.h"
#include "evaluation_result.h"

#include "plugins/plugin.h"
#include "task_utils/task_properties.h"
#include "tasks/cost_adapted_task.h"
#include "tasks/root_task.h"

#include <cassert>
#include <cstdlib>
#include <limits>

using namespace std;
Heuristic::Heuristic(
    const shared_ptr<AbstractTask> &transform,
    bool cache_estimates, const string &description,
    utils::Verbosity verbosity)
    : Evaluator(true, true, true, description, verbosity),
      heuristic_cache(HEntry(NO_VALUE, true)), //TODO: is true really a good idea here?
      cache_evaluator_values(cache_estimates),
      task(transform),
      task_proxy(*task) {
}

Heuristic::~Heuristic() {
}

void Heuristic::set_preferred(const OperatorProxy &op) {
    preferred_operators.insert(op.get_ancestor_operator_id(tasks::g_root_task.get()));
}

State Heuristic::convert_ancestor_state(const State &ancestor_state) const {
    return task_proxy.convert_ancestor_state(ancestor_state);
}

void add_heuristic_options_to_feature(
    plugins::Feature &feature, const string &description) {
    feature.add_option<shared_ptr<AbstractTask>>(
        "transform",
        "Optional task transformation for the heuristic."
        " Currently, adapt_costs() and no_transform() are available.",
        "no_transform()");
    feature.add_option<bool>("cache_estimates", "cache heuristic estimates", "true");
    add_evaluator_options_to_feature(feature, description);
}

tuple<shared_ptr<AbstractTask>, bool, string, utils::Verbosity>
get_heuristic_arguments_from_options(const plugins::Options &opts) {
    return tuple_cat(
        make_tuple(
            opts.get<shared_ptr<AbstractTask>>("transform"),
            opts.get<bool>("cache_estimates")
            ),
        get_evaluator_arguments_from_options(opts));
}

EvaluationResult Heuristic::compute_result(EvaluationContext &eval_context) {
    EvaluationResult result;

    assert(preferred_operators.empty());

    const State &state = eval_context.get_state();
    bool calculate_preferred = eval_context.get_calculate_preferred();

    int heuristic = NO_VALUE;

        state.unpack();
        vector<int> values = state.get_unpacked_values();


        for (int i=0; i<=1; ++i) {

            // Bi-reify state[x]
            ostringstream r_state_line;
            ostringstream l_state_line;
    
            for (unsigned int j = 0; j < values.size(); ++j) {
                r_state_line << " 1 " << (i ? "prime^" : "") << "var_" << j << "_"<< values[j] << " ";
                l_state_line << " 1 ~" << (i ? "prime^" : "") << "var_" << j << "_"<< values[j] << " ";
            }

            r_state_line << values.size() << " ~" << (i ? "prime^" : "") << "state[" << state.get_id_int() << "]  >= " << values.size();
            l_state_line << "1 " << (i ? "prime^" : "") << "state[" << state.get_id_int() << "]  >= 1" ;
            utils::ProofLog::append_to_proof_log(r_state_line.str(), utils::ProofPart::INVARIANT);
            utils::ProofLog::append_to_proof_log(l_state_line.str(), utils::ProofPart::INVARIANT);
        }

    if (!calculate_preferred && cache_evaluator_values &&
        heuristic_cache[state].h != NO_VALUE && !heuristic_cache[state].dirty) {
        heuristic = heuristic_cache[state].h;
        result.set_count_evaluation(false);
    } else {
        heuristic = compute_heuristic(state);
        if (cache_evaluator_values) {
            heuristic_cache[state] = HEntry(heuristic, false);
        }
        result.set_count_evaluation(true);
    }

    assert(heuristic == DEAD_END || heuristic >= 0);

    if (heuristic == DEAD_END) {
        /*
          It is permissible to mark preferred operators for dead-end
          states (thus allowing a heuristic to mark them on-the-fly
          before knowing the final result), but if it turns out we
          have a dead end, we don't want to actually report any
          preferred operators.
        */
        preferred_operators.clear();
        heuristic = EvaluationResult::INFTY;
    }

#ifndef NDEBUG
    TaskProxy global_task_proxy = state.get_task();
    OperatorsProxy global_operators = global_task_proxy.get_operators();
    if (heuristic != EvaluationResult::INFTY) {
        for (OperatorID op_id : preferred_operators)
            assert(task_properties::is_applicable(global_operators[op_id], state));
    }
#endif

    result.set_evaluator_value(heuristic);
    result.set_preferred_operators(preferred_operators.pop_as_vector());
    assert(preferred_operators.empty());

    return result;
}


void Heuristic::certify_heuristic(int return_value, State s) const {

        utils::ProofLog::append_to_proof_log(
        "*CH1 just evaluated h(s) with \n** h=" + get_description() + " "
        + "\n**CH1 s = " + to_string(s.get_id_int()) + " "
        + "\n**CH1 h(s) = " + to_string(return_value)
        , utils::ProofPart::INVARIANT);
        
        
        s.unpack();
            assert( s.get_id_int() >= 0);
            
        utils::ProofLog::add_balance_leq_x_bireification(return_value);


        for (int i=0; i<=1 ; ++i){
        // Bi-Reif node: 
            ostringstream r_node;
            ostringstream l_node;
            r_node  << endl << " * pdb NODE: Rreif of " << (i ? "" : "prime^") << "node[" << s.get_id_int() << ",balance_leq_" << return_value << "] " << endl;
            r_node << "2 ~" << (i ? "" : "prime^") << "node[" << s.get_id_int() << ",balance_leq_" << return_value << "]  1 " << (i ? "" : "prime^") << "state[" << s.get_id_int() << "]  1 " << (i ? "" : "prime^") << "balance_leq_" << return_value << "  >= 2";
            l_node << "1 " << (i ? "" : "prime^") << "node[" << s.get_id_int() << ",balance_leq_" << return_value << "]  1 ~" << (i ? "" : "prime^") << "state[" << s.get_id_int() << "]  1 ~" << (i ? "" : "prime^") << "balance_leq_" << return_value << "  >= 1";
            utils::ProofLog::append_to_proof_log(r_node.str(), utils::ProofPart::INVARIANT);
            utils::ProofLog::append_to_proof_log(l_node.str(), utils::ProofPart::INVARIANT);
        }
    // heuristic lemmas
    ostringstream entry_lemma;
    entry_lemma << endl << "* " + get_description() + " heuristic proofs:  AFTER_CH_1 btw " << endl
        << " rup  1 ~node[" << s.get_id_int() << ",balance_leq_" << return_value << "]  1 phi_" + get_description() + "[" << s.get_id_int() << "]  >= 1 ;";
    ostringstream entry_prime_lemma;
    entry_prime_lemma << " rup  1 ~prime^node[" << s.get_id_int() << ",balance_leq_" << return_value << "]  1 prime^phi_" + get_description() + "[" << s.get_id_int() << "]  >= 1 ;";
    ostringstream goal_lemma;
    goal_lemma << " rup  1 ~goal  1 balance_leq_" << 0 << "  1 ~phi_" + get_description() + "[" << s.get_id_int() << "]  >= 1 ;";
    ostringstream transition_lemma;
    transition_lemma << " rup  1 ~phi_" + get_description() + "[" << s.get_id_int() << "]  1 ~transition  1 prime^phi_" + get_description() + "[" << s.get_id_int() << "]  >= 1 ;";

    utils::ProofLog::append_to_proof_log(entry_lemma.str(), utils::ProofPart::DERIVATION);
    utils::ProofLog::append_to_proof_log(entry_prime_lemma.str(), utils::ProofPart::DERIVATION);
    utils::ProofLog::append_to_proof_log(goal_lemma.str(), utils::ProofPart::DERIVATION);
    utils::ProofLog::append_to_proof_log(transition_lemma.str(), utils::ProofPart::DERIVATION);
    
}

bool Heuristic::does_cache_estimates() const {
    return cache_evaluator_values;
}

bool Heuristic::is_estimate_cached(const State &state) const {
    return heuristic_cache[state].h != NO_VALUE;
}

int Heuristic::get_cached_estimate(const State &state) const {
    assert(is_estimate_cached(state));
    return heuristic_cache[state].h;
}
