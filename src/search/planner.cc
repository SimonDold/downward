#include "command_line.h"
#include "search_algorithm.h"

#include "tasks/root_task.h"
#include "task_utils/task_properties.h"
#include "utils/logging.h"
#include "utils/proof_logging.h"
#include "utils/system.h"
#include "utils/timer.h"

#include <chrono>
#include <iostream>

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

        remove("proof_log");

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
        auto verification_start = std::chrono::steady_clock::now();
        utils::g_log << "Start verification" << endl;
        utils::ProofLog::create_plan_pbp();
        utils::ProofLog::merge_proof_log_files(search_algorithm->get_description() + ".prooflog");
        utils::ProofLog::finalize_plan_pbp();
        int res = utils::ProofLog::runCommand("veripb plan.opb plan.pbp",
                                              "VERIFIED NO CONCLUSION");
        utils::g_log << "Stop verification with result: " << res << endl;
        auto verification_end = std::chrono::steady_clock::now();
        double verification_time =
            std::chrono::duration<double>(verification_end - verification_start).count();
        utils::g_log << "Verification time: " << verification_time << "s" << endl;

        if (res == -1 && exitcode == ExitCode::SUCCESS) {
            exitcode = ExitCode::PROOFLOG_NOT_ACCEPTED;
        }
        cout << "Proof accepted." << endl;
        exit_with(exitcode);
    } catch (const utils::ExitException &e) {
        /* To ensure that all destructors are called before the program exits,
           we raise an exception in utils::exit_with() and let main() return. */
        return static_cast<int>(e.get_exitcode());
    }
}
