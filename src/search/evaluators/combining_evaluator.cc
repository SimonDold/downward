#include "combining_evaluator.h"

#include "../evaluation_context.h"

#include "../plugins/plugin.h"

#include <utility>

using namespace std;

namespace combining_evaluator {
CombiningEvaluator::CombiningEvaluator(
    const vector<shared_ptr<Evaluator>> &evals,
    const string &description, utils::Verbosity verbosity)
    : Evaluator(false, false, false, description, verbosity),
      subevaluators(evals) {
    all_dead_ends_are_reliable = true;
    for (const shared_ptr<Evaluator> &subevaluator : subevaluators)
        if (!subevaluator->dead_ends_are_reliable())
            all_dead_ends_are_reliable = false;
}

bool CombiningEvaluator::dead_ends_are_reliable() const {
    return all_dead_ends_are_reliable;
}

EvaluationResult CombiningEvaluator::compute_result(
    EvaluationContext &eval_context) {
    // This marks no preferred operators.
    EvaluationResult result;
    vector<int> values;
    values.reserve(subevaluators.size());

    // Collect component values. Return infinity if any is infinite.
    for (const shared_ptr<Evaluator> &subevaluator : subevaluators) {
        int value = eval_context.get_evaluator_value_or_infinity(subevaluator.get());
        if (value == EvaluationResult::INFTY) {
            result.set_evaluator_value(value);
            return result;
        } else {
            values.push_back(value);
        }
    }

    // If we arrived here, all subevaluator values are finite.
    result.set_evaluator_value(combine_values(values));
    return result;
}

void CombiningEvaluator::get_path_dependent_evaluators(
    set<Evaluator *> &evals) {
    for (auto &subevaluator : subevaluators)
        subevaluator->get_path_dependent_evaluators(evals);
}


TaskIndependentCombiningEvaluator::TaskIndependentCombiningEvaluator(
    vector<shared_ptr<TaskIndependentEvaluator>> subevaluators,
    const string &description,
    utils::Verbosity verbosity)
    : TaskIndependentEvaluator(description, verbosity, false, false, false),
      subevaluators(subevaluators) {
      }

void add_combining_evaluator_options_to_feature(
    plugins::Feature &feature, const string &description) {
    feature.add_list_option<shared_ptr<TaskIndependentEvaluator>>(
        "evals", "at least one evaluator");
    add_evaluator_options_to_feature(feature, description);
}

tuple<vector<shared_ptr<TaskIndependentEvaluator>>, const string, utils::Verbosity>
get_combining_evaluator_arguments_from_options(
    const plugins::Options &opts) {
    return tuple_cat(
        make_tuple(opts.get_list<shared_ptr<TaskIndependentEvaluator>>("evals")),
        get_evaluator_arguments_from_options(opts)
        );
}
}
