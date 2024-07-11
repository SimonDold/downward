#include "g_evaluator.h"

#include "../evaluation_context.h"

#include "../plugins/plugin.h"

using namespace std;

namespace g_evaluator {
GEvaluator::GEvaluator(const string &description,
                       utils::Verbosity verbosity)
    : Evaluator(false, false, false, description, verbosity) {
}


EvaluationResult GEvaluator::compute_result(EvaluationContext &eval_context) {
    EvaluationResult result;
    result.set_evaluator_value(eval_context.get_g_value());
    return result;
}



TaskIndependentGEvaluator::TaskIndependentGEvaluator(const string &name,
                                                     utils::Verbosity verbosity)
    : TaskIndependentEvaluator(name,
                               verbosity,
                               false,
                               false,
                               false) {
}

using ConcreteProduct = GEvaluator;
using AbstractProduct = Evaluator;
using Concrete = TaskIndependentGEvaluator;
// TODO issue559 use templates as 'get_task_specific' is EXACTLY the same for all TI_Components
shared_ptr<AbstractProduct> Concrete::get_task_specific(
    [[maybe_unused]] const std::shared_ptr<AbstractTask> &task,
    std::unique_ptr<ComponentMap> &component_map,
    int depth) const {
    shared_ptr<ConcreteProduct> task_specific_x;

    if (component_map->count(static_cast<const TaskIndependentComponent *>(this))) {
        log << std::string(depth, ' ') << "Reusing task specific " << get_product_name() << " '" << description << "'..." << endl;
        task_specific_x = dynamic_pointer_cast<ConcreteProduct>(
            component_map->at(static_cast<const TaskIndependentComponent *>(this)));
    } else {
        log << std::string(depth, ' ') << "Creating task specific " << get_product_name() << " '" << description << "'..." << endl;
        task_specific_x = create_ts(task, component_map, depth);
        component_map->insert(make_pair<const TaskIndependentComponent *, std::shared_ptr<Component>>
                                  (static_cast<const TaskIndependentComponent *>(this), task_specific_x));
    }
    return task_specific_x;
}

std::shared_ptr<ConcreteProduct> Concrete::create_ts([[maybe_unused]] const shared_ptr <AbstractTask> &task,
                                                     [[maybe_unused]] unique_ptr <ComponentMap> &component_map,
                                                     [[maybe_unused]] int depth) const {
    return make_shared<GEvaluator>(description, verbosity);
}


class TaskIndependentGEvaluatorFeature : public plugins::TypedFeature<TaskIndependentEvaluator, TaskIndependentGEvaluator> {
public:
    TaskIndependentGEvaluatorFeature() : TypedFeature("g") {
        document_subcategory("evaluators_basic");
        document_title("g-value evaluator");
        document_synopsis(
            "Returns the g-value (path cost) of the search node.");
        add_evaluator_options_to_feature(*this, "g");
    }

    virtual shared_ptr<TaskIndependentGEvaluator> create_component(
        const plugins::Options &opts,
        const utils::Context &) const override {
        return plugins::make_shared_from_arg_tuples<TaskIndependentGEvaluator>(
            get_evaluator_arguments_from_options(opts)
            );
    }
};

static plugins::FeaturePlugin<TaskIndependentGEvaluatorFeature> _plugin;
}
