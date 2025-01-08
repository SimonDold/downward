#include "search_algorithm.h"

#include "evaluation_context.h"
#include "evaluator.h"

#include "algorithms/ordered_set.h"
#include "plugins/plugin.h"
#include "task_utils/successor_generator.h"
#include "task_utils/task_properties.h"
#include "tasks/root_task.h"
#include "utils/countdown_timer.h"
#include "utils/proof_logging.h"
#include "utils/rng_options.h"
#include "utils/system.h"
#include "utils/timer.h"

#include <cassert>
#include <iostream>
#include <limits>
#include <sstream>

using namespace std;
using utils::ExitCode;


static successor_generator::SuccessorGenerator &get_successor_generator(
    const TaskProxy &task_proxy, utils::LogProxy &log) {
    log << "Building successor generator..." << flush;
    int peak_memory_before = utils::get_peak_memory_in_kb();
    utils::Timer successor_generator_timer;
    successor_generator::SuccessorGenerator &successor_generator =
        successor_generator::g_successor_generators[task_proxy];
    successor_generator_timer.stop();
    log << "done!" << endl;
    int peak_memory_after = utils::get_peak_memory_in_kb();
    int memory_diff = peak_memory_after - peak_memory_before;
    log << "peak memory difference for successor generator creation: "
        << memory_diff << " KB" << endl
        << "time for successor generation creation: "
        << successor_generator_timer << endl;
    return successor_generator;
}

SearchAlgorithm::SearchAlgorithm(
    OperatorCost cost_type, int bound, double max_time,
    const string &description, utils::Verbosity verbosity)
    : description(description),
      status(IN_PROGRESS),
      solution_found(false),
      task(tasks::g_root_task),
      task_proxy(*task),
      log(utils::get_log_for_verbosity(verbosity)),
      state_registry(task_proxy),
      successor_generator(get_successor_generator(task_proxy, log)),
      search_space(state_registry, log),
      statistics(log),
      bound(bound),
      cost_type(cost_type),
      is_unit_cost(task_properties::is_unit_cost(task_proxy)),
      max_time(max_time) {
    if (bound < 0) {
        cerr << "error: negative cost bound " << bound << endl;
        utils::exit_with(ExitCode::SEARCH_INPUT_ERROR);
    }
    task_properties::print_variable_statistics(task_proxy);
}

SearchAlgorithm::SearchAlgorithm(const plugins::Options &opts) // TODO options object is needed for iterated search, the prototype for issue559 resolves this
    : description(opts.get_unparsed_config()),
      status(IN_PROGRESS),
      solution_found(false),
      task(tasks::g_root_task),
      task_proxy(*task),
      log(utils::get_log_for_verbosity(
              opts.get<utils::Verbosity>("verbosity"))),
      state_registry(task_proxy),
      successor_generator(get_successor_generator(task_proxy, log)),
      search_space(state_registry, log),
      statistics(log),
      cost_type(opts.get<OperatorCost>("cost_type")),
      is_unit_cost(task_properties::is_unit_cost(task_proxy)),
      max_time(opts.get<double>("max_time")) {
    if (opts.get<int>("bound") < 0) {
        cerr << "error: negative cost bound " << opts.get<int>("bound") << endl;
        utils::exit_with(ExitCode::SEARCH_INPUT_ERROR);
    }
    bound = opts.get<int>("bound");
    task_properties::print_variable_statistics(task_proxy);
}

SearchAlgorithm::~SearchAlgorithm() {
}

bool SearchAlgorithm::found_solution() const {
    return solution_found;
}

SearchStatus SearchAlgorithm::get_status() const {
    return status;
}

const Plan &SearchAlgorithm::get_plan() const {
    assert(solution_found);
    return plan;
}

void SearchAlgorithm::set_plan(const Plan &p) {
    solution_found = true;
    plan = p;
}

void SearchAlgorithm::search() {
    initialize();
    utils::CountdownTimer timer(max_time);
    while (status == IN_PROGRESS) {
        status = step();
        if (timer.is_expired()) {
            log << "Time limit reached. Abort search." << endl;
            status = TIMEOUT;
            break;
        }
    }
    // TODO: Revise when and which search times are logged.
    log << "Actual search time: " << timer.get_elapsed_time() << endl;
}

bool SearchAlgorithm::check_goal_and_set_plan(const State &state) {
    if (task_properties::is_goal_state(task_proxy, state)) {
        log << "Solution found!" << endl;
        Plan plan;
        search_space.trace_path(state, plan);
        set_plan(plan);
        return true;
    }
    return false;
}

void SearchAlgorithm::save_plan_if_necessary() {
    if (found_solution()) {
        plan_manager.save_plan(get_plan(), task_proxy);
    }
}

int SearchAlgorithm::get_adjusted_cost(const OperatorProxy &op) const {
    return get_adjusted_action_cost(op, cost_type, is_unit_cost);
}

// That sould be only compiled if proof_log flag is set (analogous to debug flag)

void proof_log_node_Rreif(SearchNode node, bool is_balance, bool is_prime){
    State s = node.get_state();
    s.unpack();
    assert( s.get_id_int() >= 0);
    ostringstream  reif_var, conjunct_1, conjunct_2;
    reif_var << "node[" << s.get_id_int() << "," << (is_balance ? "balance_leq_" : "spent_geq_") << node.get_g() << "]" << (is_prime ? ":" : ".");
    conjunct_1 << "state[" << s.get_id_int() << "]"                                 << (is_prime ? ":" : ".") ;
    conjunct_2 << (is_balance ? "balance_leq_" : "spent_geq_") << node.get_real_g() << (is_prime ? ":" : ".") ;
    vector<string> conjuncts = {conjunct_1.str(), conjunct_2.str()};
    utils::ProofLog::bireif_conjunction(reif_var.str(), conjuncts, "search_algo.cc/proof_log_Rreif");
    utils::ProofLog::append_to_proof_log("* the constructor of a search node should reif it... ", utils::ProofPart::REIFICATION);
}

void SearchAlgorithm::proof_log_node_reification(SearchNode node, string comment = ""){
    //TODOprooflogging name is not fitting.
    utils::ProofLog::append_to_proof_log("***proof_log_node_reification**** "+comment , utils::ProofPart::REIFICATION);
    State s = node.get_state();
    s.unpack();
    assert( s.get_id_int() >= 0);
    utils::ProofLog::add_balance_leq_x_bireification(node.get_g());
}

void SearchAlgorithm::proof_log_initialize_invar(){
    utils::ProofLog::append_to_invariant_right("@invar._Rreif red ");
    utils::ProofLog::append_to_invariant_left( "@invar._Lreif red ");
    utils::ProofLog::append_to_invariant_prime_right("@invar:_Rreif red ");
    utils::ProofLog::append_to_invariant_prime_left( "@invar:_Lreif red ");
}

void SearchAlgorithm::proof_log_extend_invar(SearchNode node, string phi_name){
    State s = node.get_state();
    s.unpack();
    assert( s.get_id_int() >= 0);
    ostringstream r_line;
    ostringstream l_line;
    r_line << " 1 ~phi_" + phi_name + "[" << s.get_id_int() << "]. " << " ";
    r_line << " 1 node[" << s.get_id_int() << ",spent_geq_" << node.get_g() << "]. " << " ";
    l_line << " 1 phi_" + phi_name + "[" << s.get_id_int() << "]. " << " ";
    l_line << " 1 ~node[" << s.get_id_int() << ",spent_geq_" << node.get_g() << "]. " << " ";
    utils::ProofLog::append_to_invariant_right(r_line.str());
    utils::ProofLog::append_to_invariant_left(l_line.str());
    // TODOprooflog remove code duplicate
    ostringstream r_prime_line;
    ostringstream l_prime_line;
    r_prime_line << " 1 ~phi_" + phi_name + "[" << s.get_id_int() << "]: " << " ";
    r_prime_line << " 1 node[" << s.get_id_int() << ",spent_geq_" << node.get_g() << "]: " << " ";
    l_prime_line << " 1 phi_" + phi_name + "[" << s.get_id_int() << "]: " << " ";
    l_prime_line << " 1 ~node[" << s.get_id_int() << ",spent_geq_" << node.get_g() << "]: " << " ";
    utils::ProofLog::append_to_invariant_prime_right(r_prime_line.str());
    utils::ProofLog::append_to_invariant_prime_left(l_prime_line.str());
}

void SearchAlgorithm::proof_log_finalize_invar(int expanded, int evaluated, SearchNode node, string phi_name){
    State s = node.get_state();

    int A = expanded;
    int M = 2 * expanded + evaluated; // expaination needed
    int A2 = 1;
    int M2 = evaluated;

    for (int i = 0; i<=1; ++i){
        ostringstream r_prime_line;
        ostringstream l_prime_line;

        r_prime_line << " 1 " << "phi_" + phi_name + "[" << s.get_id_int() << "]" << (i ? ":" : ".") << " ";
        l_prime_line << " 1 ~"<< "phi_" + phi_name + "[" << s.get_id_int() << "]" << (i ? ":" : ".") << " ";

        r_prime_line <<           A+1 << " ~" << "invar" << (i ? ":" : ".") << " >= " <<    A+1 << " , invar" << (i ? ":" : ".") << " -> 0" << endl;
        l_prime_line << " " << A+M2+1 << " "  << "invar" << (i ? ":" : ".") << " >= " << A+M2+1 << " , invar" << (i ? ":" : ".") << " -> 1" << endl;
        l_prime_line << "* expanded = " << expanded << endl << "* evaluated = " << evaluated << endl;
        l_prime_line << "* A = " << A << endl << "* M = " << M << endl;
        l_prime_line << "* A2 = " << A2 << endl << "* M2 = " << M2 << endl;
        if (i) {
            utils::ProofLog::append_to_invariant_prime_right(r_prime_line.str());
            utils::ProofLog::append_to_invariant_prime_left(l_prime_line.str());
        } else{
            utils::ProofLog::append_to_invariant_right(r_prime_line.str());
            utils::ProofLog::append_to_invariant_left(l_prime_line.str());
        }
    }
}

void SearchAlgorithm::proof_log_reif_state(State s){ //TODOprooflogging This should happen in the state constructor... but it is complicated with the packed and partially packt constructors
    s.unpack();
    assert(s.get_id_int() >= 0);
    vector<int> values = s.get_unpacked_values();
    vector<string> conjuncts(values.size());
    for (bool p : {false, true}) {
        string prime = (p ? "." : ":"); 
        for (int i = 0; i < values.size(); ++i){
            conjuncts[i] = "var_" + to_string(i) + "_" + to_string(values[i]) + prime;
        }
        utils::ProofLog::bireif_conjunction("state["+to_string(s.get_id_int())+"]"+prime, conjuncts, "bireif state");
    }
}

void SearchAlgorithm::proof_log_node_action_invariant(OperatorID op_id, SearchNode node){
    OperatorsProxy operators = task_proxy.get_operators();
    State s = node.get_state();
    s.unpack();
            assert( s.get_id_int() >= 0);
    ostringstream line;
    line << endl << "rup  1 ~node[" << s.get_id_int() << ",spent_geq_" << node.get_g() << "]  1 ~op_" << operators[op_id].get_id() << "  1 prime^invar >= 1;";
    utils::ProofLog::append_to_proof_log(line.str(), utils::ProofPart::DERIVATION);
}

void SearchAlgorithm::proof_log_node_transition_invariant(SearchNode node) {
    State s = node.get_state();
    ostringstream line;
    line << "rup  1 ~node[" << s.get_id_int() << ",spent_geq_" << node.get_g() << "]  1 ~transition  1 prime^invar >= 1;";
    utils::ProofLog::append_to_proof_log(line.str(), utils::ProofPart::DERIVATION);
}

void print_initial_evaluator_values(
    const EvaluationContext &eval_context) {
    eval_context.get_cache().for_each_evaluator_result(
        [] (const Evaluator *eval, const EvaluationResult &result) {
            if (eval->is_used_for_reporting_minima()) {
                eval->report_value_for_initial_state(result);
            }
        }
        );
}

/* TODO: merge this into add_options_to_feature when all search
         algorithms support pruning.

   Method doesn't belong here because it's only useful for certain derived classes.
   TODO: Figure out where it belongs and move it there. */
void add_search_pruning_options_to_feature(plugins::Feature &feature) {
    feature.add_option<shared_ptr<PruningMethod>>(
        "pruning",
        "Pruning methods can prune or reorder the set of applicable operators in "
        "each state and thereby influence the number and order of successor states "
        "that are considered.",
        "null()");
}

tuple<shared_ptr<PruningMethod>>
get_search_pruning_arguments_from_options(
    const plugins::Options &opts) {
    return make_tuple(opts.get<shared_ptr<PruningMethod>>("pruning"));
}

void add_search_algorithm_options_to_feature(
    plugins::Feature &feature, const string &description) {
    ::add_cost_type_options_to_feature(feature);
    feature.add_option<int>(
        "bound",
        "exclusive depth bound on g-values. Cutoffs are always performed according to "
        "the real cost, regardless of the cost_type parameter", "infinity");
    feature.add_option<double>(
        "max_time",
        "maximum time in seconds the search is allowed to run for. The "
        "timeout is only checked after each complete search step "
        "(usually a node expansion), so the actual runtime can be arbitrarily "
        "longer. Therefore, this parameter should not be used for time-limiting "
        "experiments. Timed-out searches are treated as failed searches, "
        "just like incomplete search algorithms that exhaust their search space.",
        "infinity");
    feature.add_option<string>(
        "description",
        "description used to identify search algorithm in logs",
        "\"" + description + "\"");
    utils::add_log_options_to_feature(feature);
}

tuple<OperatorCost, int, double, string, utils::Verbosity>
get_search_algorithm_arguments_from_options(
    const plugins::Options &opts) {
    return tuple_cat(
        ::get_cost_type_arguments_from_options(opts),
        make_tuple(
            opts.get<int>("bound"),
            opts.get<double>("max_time"),
            opts.get<string>("description")
            ),
        utils::get_log_arguments_from_options(opts)
        );
}

/* Method doesn't belong here because it's only useful for certain derived classes.
   TODO: Figure out where it belongs and move it there. */
void add_successors_order_options_to_feature(
    plugins::Feature &feature) {
    feature.add_option<bool>(
        "randomize_successors",
        "randomize the order in which successors are generated",
        "false");
    feature.add_option<bool>(
        "preferred_successors_first",
        "consider preferred operators first",
        "false");
    feature.document_note(
        "Successor ordering",
        "When using randomize_successors=true and "
        "preferred_successors_first=true, randomization happens before "
        "preferred operators are moved to the front.");
    utils::add_rng_options_to_feature(feature);
}

tuple<bool, bool, int> get_successors_order_arguments_from_options(
    const plugins::Options &opts) {
    return tuple_cat(
        make_tuple(
            opts.get<bool>("randomize_successors"),
            opts.get<bool>("preferred_successors_first")
            ),
        utils::get_rng_arguments_from_options(opts)
        );
}

static class SearchAlgorithmCategoryPlugin : public plugins::TypedCategoryPlugin<SearchAlgorithm> {
public:
    SearchAlgorithmCategoryPlugin() : TypedCategoryPlugin("SearchAlgorithm") {
        // TODO: Replace add synopsis for the wiki page.
        // document_synopsis("...");
    }
}
_category_plugin;

void collect_preferred_operators(
    EvaluationContext &eval_context,
    Evaluator *preferred_operator_evaluator,
    ordered_set::OrderedSet<OperatorID> &preferred_operators) {
    if (!eval_context.is_evaluator_value_infinite(preferred_operator_evaluator)) {
        for (OperatorID op_id : eval_context.get_preferred_operators(preferred_operator_evaluator)) {
            preferred_operators.insert(op_id);
        }
    }
}
