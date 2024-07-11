#include "best_first_open_list.h"

#include "../evaluator.h"
#include "../open_list.h"

#include "../plugins/plugin.h"
#include "../utils/memory.h"

#include <cassert>

using namespace std;

namespace standard_scalar_open_list {

template<class Entry>
void BestFirstOpenList<Entry>::do_insertion(
    EvaluationContext &eval_context, const Entry &entry) {
    int key = eval_context.get_evaluator_value(evaluator.get());
    buckets[key].push_back(entry);
    ++size;
}

template<class Entry>
Entry BestFirstOpenList<Entry>::remove_min() {
    assert(size > 0);
    auto it = buckets.begin();
    assert(it != buckets.end());
    Bucket &bucket = it->second;
    assert(!bucket.empty());
    Entry result = bucket.front();
    bucket.pop_front();
    if (bucket.empty())
        buckets.erase(it);
    --size;
    return result;
}

template<class Entry>
bool BestFirstOpenList<Entry>::empty() const {
    return size == 0;
}

template<class Entry>
void BestFirstOpenList<Entry>::clear() {
    buckets.clear();
    size = 0;
}

template<class Entry>
void BestFirstOpenList<Entry>::get_path_dependent_evaluators(
    set<Evaluator *> &evals) {
    evaluator->get_path_dependent_evaluators(evals);
}

template<class Entry>
bool BestFirstOpenList<Entry>::is_dead_end(
    EvaluationContext &eval_context) const {
    return eval_context.is_evaluator_value_infinite(evaluator.get());
}

template<class Entry>
bool BestFirstOpenList<Entry>::is_reliable_dead_end(
    EvaluationContext &eval_context) const {
    return is_dead_end(eval_context) && evaluator->dead_ends_are_reliable();
}

BestFirstOpenListFactory::BestFirstOpenListFactory(
    const shared_ptr<Evaluator> &eval, bool pref_only)
    : eval(eval),
      pref_only(pref_only) {
}

unique_ptr<StateOpenList>
BestFirstOpenListFactory::create_state_open_list() {
    return utils::make_unique_ptr<BestFirstOpenList<StateOpenListEntry>>(
        eval, pref_only);
}

unique_ptr<EdgeOpenList>
BestFirstOpenListFactory::create_edge_open_list() {
    return make_unique<BestFirstOpenList<EdgeOpenListEntry>>(eval, pref_only);
}

TaskIndependentBestFirstOpenListFactory::TaskIndependentBestFirstOpenListFactory(
    shared_ptr<TaskIndependentEvaluator> evaluator, bool pref_only)
    : TaskIndependentOpenListFactory("TieBreakingOpenListFactory", utils::Verbosity::NORMAL),
      pref_only(pref_only), size(0), evaluator(evaluator) {
}


using ConcreteProduct = BestFirstOpenListFactory;
using AbstractProduct = OpenListFactory;
using Concrete = TaskIndependentBestFirstOpenListFactory;
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

std::shared_ptr<ConcreteProduct> Concrete::create_ts(const shared_ptr <AbstractTask> &task,
                                                     unique_ptr <ComponentMap> &component_map, int depth) const {
    return make_shared<BestFirstOpenListFactory>(
        evaluator->get_task_specific(task, component_map, depth >= 0 ? depth + 1 : depth),
        pref_only);
}


class BestFirstOpenListFeature
    : public plugins::TypedFeature<TaskIndependentOpenListFactory, TaskIndependentBestFirstOpenListFactory> {
public:
    BestFirstOpenListFeature() : TypedFeature("single") {
        document_title("Best-first open list");
        document_synopsis(
            "Open list that uses a single evaluator and FIFO tiebreaking.");

        add_option<shared_ptr<TaskIndependentEvaluator>>("eval", "evaluator");
        add_open_list_options_to_feature(*this);

        document_note(
            "Implementation Notes",
            "Elements with the same evaluator value are stored in double-ended "
            "queues, called \"buckets\". The open list stores a map from evaluator "
            "values to buckets. Pushing and popping from a bucket runs in constant "
            "time. Therefore, inserting and removing an entry from the open list "
            "takes time O(log(n)), where n is the number of buckets.");
    }
    virtual shared_ptr<TaskIndependentBestFirstOpenListFactory> create_component(
        const plugins::Options &opts,
        const utils::Context &) const override {
        return plugins::make_shared_from_arg_tuples<TaskIndependentBestFirstOpenListFactory>(
            opts.get<shared_ptr<TaskIndependentEvaluator>>("eval"),
            get_open_list_arguments_from_options(opts));
    }
};

static plugins::FeaturePlugin<BestFirstOpenListFeature> _plugin;
}
