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
    bool cache_estimates,
    const string &description,
    utils::Verbosity verbosity)
    : Evaluator(true, true, true, description, verbosity),
      heuristic_cache(HEntry(NO_VALUE, true)),     //TODO: is true really a good idea here?
      cache_evaluator_values(cache_estimates),
      task(transform),
      task_proxy(*task) {
}

// TODO 1082 remove this, just keep the one above
Heuristic::Heuristic(const plugins::Options &opts)
    : Evaluator(opts, true, true, true),
      heuristic_cache(HEntry(NO_VALUE, true)), //TODO: is true really a good idea here?
      cache_evaluator_values(opts.get<bool>("cache_estimates")),
      task(opts.get<shared_ptr<AbstractTask>>("transform")),
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

void Heuristic::add_options_to_feature(plugins::Feature &feature, const string &description) {
    feature.add_option<shared_ptr<AbstractTask>>(
        "transform",
        "Optional task transformation for the heuristic."
        " Currently, adapt_costs() and no_transform() are available.",
        "no_transform()");
    feature.add_option<bool>("cache_estimates", "cache heuristic estimates", "true");
    add_evaluator_options_to_feature(feature, description);
}

// TODO 1082 remove this, just keep the one above
void Heuristic::add_options_to_feature(plugins::Feature &feature) {
    feature.add_option<shared_ptr<AbstractTask>>(
        "transform",
        "Optional task transformation for the heuristic."
        " Currently, adapt_costs() and no_transform() are available.",
        "no_transform()");
    feature.add_option<bool>("cache_estimates", "cache heuristic estimates", "true");
    add_evaluator_options_to_feature(feature);
}


shared_ptr<tuple<shared_ptr<AbstractTask>, bool, string, utils::Verbosity>> Heuristic::get_heuristic_parameters_from_options(const plugins::Options &opts) {
    auto parent_parameter_tuple = get_evaluator_parameters_from_options(opts);
    auto own_parameter_tuple = make_tuple(
        opts.get<shared_ptr<AbstractTask>>("transform"),
        opts.get<bool>("cache_estimates")
        );
    return make_shared<tuple<shared_ptr<AbstractTask>, bool, string, utils::Verbosity>>(tuple_cat(own_parameter_tuple, *parent_parameter_tuple));
}

EvaluationResult Heuristic::compute_result(EvaluationContext &eval_context) {
    EvaluationResult result;

    assert(preferred_operators.empty());

    const State &state = eval_context.get_state();
    bool calculate_preferred = eval_context.get_calculate_preferred();

    int heuristic = NO_VALUE;

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

shared_ptr<tuple<shared_ptr<AbstractTask>, bool, string, utils::Verbosity>> Heuristic::get_own_parameters_from_options(const plugins::Options &opts) {
    auto parent_parameter_tuple = Evaluator::get_own_parameters_from_options(opts);
    auto own_parameter_tuple = make_tuple(
            opts.get<shared_ptr<AbstractTask>>("transform"),
            opts.get<bool>("cache_estimates")
    );
    return make_shared<tuple<shared_ptr<AbstractTask>, bool, string, utils::Verbosity>>(tuple_cat(own_parameter_tuple, *parent_parameter_tuple));
}

template<typename ConcreteComponent, typename ParentComponent, typename ...Args>
std::shared_ptr<ConcreteComponent> make_shared_by_magic(const plugins::Options &opts, Args ... args){
    tuple<Args...> child_tuple = make_tuple<Args...>(args...);
    tuple own_tuple = make_shared(ParentComponent::get_own_parameters_from_options(opts));

    tuple full_tuple = tuple_cat(child_tuple, own_tuple);
    plugins::make_shared_from_tuple<ConcreteComponent>(full_tuple)
}