#include "blind_search_heuristic.h"

#include "../plugins/plugin.h"

#include "../task_utils/task_properties.h"
#include "../utils/logging.h"
#include "../utils/proof_logging.h"

#include <cstddef>
#include <limits>
#include <utility>

using namespace std;

namespace blind_search_heuristic {
BlindSearchHeuristic::BlindSearchHeuristic(
    const shared_ptr<AbstractTask> &transform, bool cache_estimates,
    const string &description, utils::Verbosity verbosity)
    : Heuristic(transform, cache_estimates, description, verbosity),
      min_operator_cost(
          task_properties::get_min_operator_cost(task_proxy)) {
    if (log.is_at_least_normal()) {
        log << "Initializing blind search heuristic..." << endl;
    }
}

int BlindSearchHeuristic::compute_heuristic(const State &ancestor_state) {
    State state = convert_ancestor_state(ancestor_state);
    if (task_properties::is_goal_state(task_proxy, state)) {
        return 0;
    } else {
        /*
        add reification of phi[state,g] but i dont have the g value :(
        atm i am cheating inside of TieBreakingOpenList<Entry>::do_insertion
        */

        State s = ancestor_state;
        s.unpack();
            assert( s.get_id_int() >= 0);
               // this belongs to blind heuristic
        utils::ProofLog::add_balance_leq_x_bireification(min_operator_cost);
        int bits = 8;//proof_log_var_count + proof_log_max_cost_bits;
        ostringstream derivation_line;
        derivation_line << endl << "pol  @balance_leq_" << (min_operator_cost) << "_Rreif  @prime^balance_leq_" << (min_operator_cost) << "_Lreif  +  @delta_cost_geq_MIN_Rreif  +  " << (1 << bits) << " d ;";
        utils::ProofLog::append_to_proof_log(derivation_line.str(), utils::ProofPart::DERIVATION);

        for (int i=0; i<=1 ; ++i){
            ostringstream r_line;
            ostringstream l_line;
            r_line  << endl << " * Rreif of " << (i ? "" : "prime^") << "phi[" << s.get_id_int() << "] " << endl;
            r_line << "1 ~" << (i ? "" : "prime^") << "phi[" << s.get_id_int() << "]  1 " << (i ? "" : "prime^") << "node[" << s.get_id_int() << ",balance_leq_" << min_operator_cost << "]  1 " << (i ? "" : "prime^") << "balance_leq_" << 0 << "  >= 1";
            l_line << " * Lreif of " << (i ? "" : "prime^") << "phi[" << s.get_id_int() << "]" << endl;
            l_line << "2 " << (i ? "" : "prime^") << "phi[" << s.get_id_int() << "]  1 ~" << (i ? "" : "prime^") << "node[" << s.get_id_int() << ",balance_leq_" << min_operator_cost << "]  1 ~" << (i ? "" : "prime^") << "balance_leq_" << 0 << "  >= 2";
            utils::ProofLog::append_to_proof_log(r_line.str(), utils::ProofPart::INVARIANT);
            utils::ProofLog::append_to_proof_log(l_line.str(), utils::ProofPart::INVARIANT);
        }

        ostringstream entry_lemma;
        entry_lemma << endl << "* heuristic proofs:" << endl << "rup  1 ~node[" << s.get_id_int() << ",balance_leq_" << min_operator_cost << "]  1 phi[" << s.get_id_int() << "]  >= 1 ;";
        ostringstream entry_prime_lemma;
        entry_prime_lemma << "rup  1 ~prime^node[" << s.get_id_int() << ",balance_leq_" << min_operator_cost << "]  1 prime^phi[" << s.get_id_int() << "]  >= 1 ;";
        ostringstream goal_lemma;
        goal_lemma << "rup  1 ~goal  1 balance_leq_" << min_operator_cost << "  1 ~phi[" << s.get_id_int() << "]  >= 1 ;";
        ostringstream transition_lemma;
        transition_lemma << "rup  1 ~phi[" << s.get_id_int() << "]  1 ~transition  1 prime^phi[" << s.get_id_int() << "]  >= 1 ;";

        utils::ProofLog::append_to_proof_log(entry_lemma.str(), utils::ProofPart::DERIVATION);
        utils::ProofLog::append_to_proof_log(entry_prime_lemma.str(), utils::ProofPart::DERIVATION);
        utils::ProofLog::append_to_proof_log(goal_lemma.str(), utils::ProofPart::DERIVATION);
        utils::ProofLog::append_to_proof_log(transition_lemma.str(), utils::ProofPart::DERIVATION);


        return min_operator_cost;
    }
}

class BlindSearchHeuristicFeature
    : public plugins::TypedFeature<Evaluator, BlindSearchHeuristic> {
public:
    BlindSearchHeuristicFeature() : TypedFeature("blind") {
        document_title("Blind heuristic");
        document_synopsis(
            "Returns cost of cheapest action for non-goal states, "
            "0 for goal states");

        add_heuristic_options_to_feature(*this, "blind");

        document_language_support("action costs", "supported");
        document_language_support("conditional effects", "supported");
        document_language_support("axioms", "supported");

        document_property("admissible", "yes");
        document_property("consistent", "yes");
        document_property("safe", "yes");
        document_property("preferred operators", "no");
    }

    virtual shared_ptr<BlindSearchHeuristic> create_component(
        const plugins::Options &opts,
        const utils::Context &) const override {
        return plugins::make_shared_from_arg_tuples<BlindSearchHeuristic>(
            get_heuristic_arguments_from_options(opts)
            );
    }
};

static plugins::FeaturePlugin<BlindSearchHeuristicFeature> _plugin;
}
