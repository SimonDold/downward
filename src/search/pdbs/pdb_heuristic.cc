#include "pdb_heuristic.h"

#include "pattern_database.h"

#include "../plugins/plugin.h"
#include "../utils/markup.h"

#include <limits>
#include <memory>

using namespace std;

namespace pdbs {
static shared_ptr<PatternDatabase> get_pdb_from_generator(
    const shared_ptr<AbstractTask> &task,
    const shared_ptr<PatternGenerator> &pattern_generator) {
    PatternInformation pattern_info = pattern_generator->generate(task);
    return pattern_info.get_pdb();
}

PDBHeuristic::PDBHeuristic(
    const shared_ptr<PatternGenerator> &pattern,
    const shared_ptr<AbstractTask> &transform, bool cache_estimates,
    const string &description, utils::Verbosity verbosity)
    : Heuristic(transform, cache_estimates, description, verbosity),
      pdb(get_pdb_from_generator(task, pattern)) {
}

void PDBHeuristic::certify_heuristic_pdb(int return_value, State s) {

        s.unpack();
            assert( s.get_id_int() >= 0);
            
        utils::ProofLog::add_balance_leq_x_bireification(return_value);

        for (int i=0; i<=1 ; ++i){

        // Bi-Reif phi(node,heuristic): 
            ostringstream r_line;
            ostringstream l_line;
            r_line  << endl << " *pdb PHI: Rreif of " << (i ? "" : "prime^") << "phi_" + get_description() + "[" << s.get_id_int() << "] " << endl;
            r_line << "1 ~" << (i ? "" : "prime^") << "phi_" + get_description() + "[" << s.get_id_int() << "]  1 ~" << (i ? "" : "prime^") << "rev_indu  >= 1";
            l_line << " *pdb PHI: Lreif of " << (i ? "" : "prime^") << "phi_" + get_description() + "[" << s.get_id_int() << "]" << endl;
            l_line << "1 " << (i ? "" : "prime^") << "phi_" + get_description() + "[" << s.get_id_int() << "]  1 " << (i ? "" : "prime^") << "rev_indu  >= 1";
            utils::ProofLog::append_to_proof_log(r_line.str(), utils::ProofPart::INVARIANT);
            utils::ProofLog::append_to_proof_log(l_line.str(), utils::ProofPart::INVARIANT);
        }
}


int PDBHeuristic::compute_heuristic(const State &ancestor_state) {
    State state = convert_ancestor_state(ancestor_state);
    int h = pdb->get_value(state.get_unpacked_values());
    if (h == numeric_limits<int>::max()) {
        return DEAD_END;
    }
    certify_heuristic_pdb(h, ancestor_state);
    certify_heuristic(h, ancestor_state);
    return h;
}

static basic_string<char> paper_references() {
    return utils::format_conference_reference(
        {"Stefan Edelkamp"},
        "Planning with Pattern Databases",
        "https://aaai.org/papers/7280-ecp-01-2001/",
        "Proceedings of the Sixth European Conference on Planning (ECP 2001)",
        "84-90",
        "AAAI Press",
        "2001") +
           "For implementation notes, see:" + utils::format_conference_reference(
        {"Silvan Sievers", "Manuela Ortlieb", "Malte Helmert"},
        "Efficient Implementation of Pattern Database Heuristics for"
        " Classical Planning",
        "https://ai.dmi.unibas.ch/papers/sievers-et-al-socs2012.pdf",
        "Proceedings of the Fifth Annual Symposium on Combinatorial"
        " Search (SoCS 2012)",
        "105-111",
        "AAAI Press",
        "2012");
}
class PDBHeuristicFeature
    : public plugins::TypedFeature<Evaluator, PDBHeuristic> {
public:
    PDBHeuristicFeature() : TypedFeature("pdb") {
        document_subcategory("heuristics_pdb");
        document_title("Pattern database heuristic");
        document_synopsis(
            "Computes goal distance in "
            "state space abstractions based on projections. "
            "First used in domain-independent planning by:"
            + paper_references());

        add_option<shared_ptr<PatternGenerator>>(
            "pattern",
            "pattern generation method",
            "greedy()");
        add_heuristic_options_to_feature(*this, "pdb");

        document_language_support("action costs", "supported");
        document_language_support("conditional effects", "not supported");
        document_language_support("axioms", "not supported");

        document_property("admissible", "yes");
        document_property("consistent", "yes");
        document_property("safe", "yes");
        document_property("preferred operators", "no");
    }

    virtual shared_ptr<PDBHeuristic> create_component(
        const plugins::Options &opts,
        const utils::Context &) const override {
        return plugins::make_shared_from_arg_tuples<PDBHeuristic>(
            opts.get<shared_ptr<PatternGenerator>>("pattern"),
            get_heuristic_arguments_from_options(opts)
            );
    }
};

static plugins::FeaturePlugin<PDBHeuristicFeature> _plugin;
}
