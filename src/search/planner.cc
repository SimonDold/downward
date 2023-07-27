#include "command_line.h"
#include "search_algorithm.h"

#include "tasks/root_task.h"
#include "task_utils/task_properties.h"
#include "utils/logging.h"
#include "utils/system.h"
#include "utils/timer.h"

#include <iostream>


#include "task_independent_search_algorithm.h"
//for testing

#include "heuristics/lm_cut_heuristic.h"
#include "evaluators/g_evaluator.h"

using namespace std;
using utils::ExitCode;

int main(int argc, const char **argv) {
    try {
        utils::register_event_handlers();

        if (argc < 2) {
            utils::g_log << usage(argv[0]) << endl;
            utils::exit_with(ExitCode::SEARCH_INPUT_ERROR);
        }

        bool unit_cost = false;
        if (static_cast<string>(argv[1]) != "--help") {
            utils::g_log << "reading input..." << endl;
            tasks::read_root_task(cin);
            utils::g_log << "done reading input!" << endl;
            TaskProxy task_proxy(*tasks::g_root_task);
            unit_cost = task_properties::is_unit_cost(task_proxy);
        }

        shared_ptr<SearchAlgorithm> search_algorithm =
            parse_cmd_line(argc, argv, unit_cost);


        utils::Timer search_timer;
        search_algorithm->search();
        search_timer.stop();
        utils::g_timer.stop();

        search_algorithm->save_plan_if_necessary();
        search_algorithm->print_statistics();
        utils::g_log << "Search time: " << search_timer << endl;
        utils::g_log << "Total time: " << utils::g_timer << endl;

        ExitCode exitcode = search_algorithm->found_solution()
            ? ExitCode::SUCCESS
            : ExitCode::SEARCH_UNSOLVED_INCOMPLETE;
        exit_with(exitcode);
    } catch (const utils::ExitException &e) {
        /* To ensure that all destructors are called before the program exits,
           we raise an exception in utils::exit_with() and let main() return. */
        return static_cast<int>(e.get_exitcode());
    }

    bool unit_cost = false;
    if (static_cast<string>(argv[1]) != "--help") {
        utils::g_log << "reading input..." << endl;
        tasks::read_root_task(cin);
        utils::g_log << "done reading input!" << endl;
        TaskProxy task_proxy(*tasks::g_root_task);
        unit_cost = task_properties::is_unit_cost(task_proxy);
    }

    //start testing
    std::string _unparsed_config = std::string();
    utils::LogProxy _log = get_log_from_verbosity(utils::Verbosity::NORMAL);
    bool _cache_evaluator_values = false;
    //test lmc
    shared_ptr<lm_cut_heuristic::TaskIndependentLandmarkCutHeuristic> ti_lmcut =
            make_shared<lm_cut_heuristic::TaskIndependentLandmarkCutHeuristic>(_unparsed_config,
                                                                               _log,
                                                                               _cache_evaluator_values);
    shared_ptr<Evaluator> lmcut =  ti_lmcut->create_task_specific(tasks::g_root_task);
    cout << "" << lmcut->get_description() << "," << lmcut->is_used_for_boosting() << endl;
    cout << " \\o/ \\o/ \\o/ \\o/ \\o/ \\o/ LMC SUCCESS \\o/" << endl;

    //test g
    shared_ptr<g_evaluator::TaskIndependentGEvaluator> ti_g =
            make_shared<g_evaluator::TaskIndependentGEvaluator>(_log,
                                                                _unparsed_config,
                                                                _cache_evaluator_values);
    shared_ptr<Evaluator> g =  ti_g->create_task_specific(tasks::g_root_task);
    cout << "" << g->get_description() << "," << g->is_used_for_boosting() << endl;
    cout << " \\o/ \\o/ \\o/ \\o/ \\o/ \\o/ G SUCCESS \\o/" << endl;


    //shared_ptr<TaskIndependentGEval> ti_geval = make_shared<TaskIndependentGEval>(arg1, arg2);
    //shared_ptr<GEval> geval = ti_geval.specify(tasks::g_root_task);
    cout << " \\o/ \\o/ \\o/ \\o/ \\o/ \\o/ \\o/ \\o/ \\o/ \\o/ \\o/ \\o/ TEST SUCCESS \\o/" << endl;
    cout << "!!!!!!!!!!!THIS WAS A TEST RUN!!!!!!!!!!!!!!" << endl;

    exit(0);
    //end testing


    shared_ptr<TaskIndependentSearchAlgorithm> ti_search_algorithm = parse_cmd_line(argc, argv, unit_cost);
    //shared_ptr<SearchAlgorithm> search_algorithm = ti_search_algorithm->create_task_specific(tasks::g_root_task);
    shared_ptr<SearchAlgorithm> search_algorithm(nullptr);

    utils::Timer search_timer;
    search_algorithm->search();
    search_timer.stop();
    utils::g_timer.stop();

    search_algorithm->save_plan_if_necessary();
    search_algorithm->print_statistics();
    utils::g_log << "Search time: " << search_timer << endl;
    utils::g_log << "Total time: " << utils::g_timer << endl;

    ExitCode exitcode = search_algorithm->found_solution()
        ? ExitCode::SUCCESS
        : ExitCode::SEARCH_UNSOLVED_INCOMPLETE;
    utils::report_exit_code_reentrant(exitcode);
    return static_cast<int>(exitcode);
}
