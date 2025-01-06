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
    int return_value;
    if (task_properties::is_goal_state(task_proxy, state)) {
        return_value = 0;
    } else {
        return_value = min_operator_cost;
    }
    certify_heuristic(return_value, ancestor_state);
        /*
        add reification of phi[state,g] but i dont have the g value :(
        atm i am cheating inside of TieBreakingOpenList<Entry>::do_insertion
        */

        // TODOprooflogging move to encapsulated method.
        State s = ancestor_state;
        s.unpack();
            assert( s.get_id_int() >= 0);
               // this belongs to blind heuristic
        utils::ProofLog::add_balance_leq_x_bireification(return_value);
        int bits = utils::ProofLog::get_proof_log_bits();
        ostringstream derivation_line;
        derivation_line << endl << "pol  @balance_leq_" << (return_value) << "_Rreif  @prime^balance_leq_" << (return_value) << "_Lreif  +  @delta_cost_geq_MIN_Rreif  +  " << (1 << bits) << " d ;";
        assert((1 << bits)>=0); // no overflow
        utils::ProofLog::append_to_proof_log(derivation_line.str(), utils::ProofPart::DERIVATION);

        
        for (int i=0; i<=1 ; ++i){

        // Bi-Reif phi(node,heuristic): 
            ostringstream r_line;
            ostringstream l_line;
            r_line  << endl << " *blind: Rreif of " << (i ? "" : "prime^") << "phi_" + get_description() + "[" << s.get_id_int() << "] " << endl;
            r_line << "1 ~" << (i ? "" : "prime^") << "phi_" + get_description() + "[" << s.get_id_int() << "]  1 " << (i ? "" : "prime^") << "node[" << s.get_id_int() << ",balance_leq_" << return_value << "]  1 " << (i ? "" : "prime^") << "balance_leq_" << 0 << "  >= 1";
            l_line << " *blind: Lreif of " << (i ? "" : "prime^") << "phi_" + get_description() + "[" << s.get_id_int() << "]" << endl;
            l_line << "2 " << (i ? "" : "prime^") << "phi_" + get_description() + "[" << s.get_id_int() << "]  1 ~" << (i ? "" : "prime^") << "node[" << s.get_id_int() << ",balance_leq_" << return_value << "]  1 ~" << (i ? "" : "prime^") << "balance_leq_" << 0 << "  >= 2";
            utils::ProofLog::append_to_proof_log(r_line.str(), utils::ProofPart::INVARIANT);
            utils::ProofLog::append_to_proof_log(l_line.str(), utils::ProofPart::INVARIANT);
        }

    return return_value;
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
