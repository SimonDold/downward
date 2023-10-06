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
    const plugins::Options &options)
    : options(options) {
}

BestFirstOpenListFactory::BestFirstOpenListFactory(bool pref_only, shared_ptr<Evaluator> evaluator)
    : pref_only(pref_only), size(0),
      evaluator(evaluator) {
}


unique_ptr<StateOpenList>
BestFirstOpenListFactory::create_state_open_list() {
    return make_unique<BestFirstOpenList<StateOpenListEntry>>(options);
}

unique_ptr<EdgeOpenList>
BestFirstOpenListFactory::create_edge_open_list() {
    return make_unique<BestFirstOpenList<EdgeOpenListEntry>>(options);
}

TaskIndependentBestFirstOpenListFactory::TaskIndependentBestFirstOpenListFactory(const plugins::Options &opts)
    : pref_only(opts.get<bool>("pref_only")),
      size(0),
      evaluator(opts.get<std::shared_ptr<TaskIndependentEvaluator>>("eval")),
      options(opts) {
}

TaskIndependentBestFirstOpenListFactory::TaskIndependentBestFirstOpenListFactory(
    bool pref_only, shared_ptr<TaskIndependentEvaluator> evaluator
    )
    : pref_only(pref_only), size(0), evaluator(evaluator) {
}


shared_ptr<BestFirstOpenListFactory> TaskIndependentBestFirstOpenListFactory::create_task_specific_BestFirstOpenListFactory(const shared_ptr<AbstractTask> &task, std::unique_ptr<ComponentMap> &component_map, int depth) {
    shared_ptr<BestFirstOpenListFactory> task_specific_x;
    if (component_map->contains_key(make_pair(task, static_cast<void *>(this)))) {
        utils::g_log << std::string(depth, ' ') << "Reusing task specific BestFirstOpenListFactory..." << endl;
        task_specific_x = plugins::any_cast<shared_ptr<BestFirstOpenListFactory>>(
            component_map->get_dual_key_value(task, this));
    } else {
        utils::g_log << std::string(depth, ' ') << "Creating task specific BestFirstOpenListFactory..." << endl;

        task_specific_x = make_shared<BestFirstOpenListFactory>(pref_only, evaluator->create_task_specific_Evaluator(task, component_map, depth >= 0 ? depth + 1 : depth));
        component_map->add_dual_key_entry(task, this, plugins::Any(task_specific_x));
    }
    return task_specific_x;
}


shared_ptr<BestFirstOpenListFactory> TaskIndependentBestFirstOpenListFactory::create_task_specific_BestFirstOpenListFactory(const shared_ptr<AbstractTask> &task, int depth) {
    std::unique_ptr<ComponentMap> component_map = std::make_unique<ComponentMap>();
    return create_task_specific_BestFirstOpenListFactory(task, component_map, depth);
}


shared_ptr<OpenListFactory> TaskIndependentBestFirstOpenListFactory::create_task_specific_OpenListFactory(const shared_ptr<AbstractTask> &task, unique_ptr<ComponentMap> &component_map, int depth) {
    utils::g_log << std::string(depth, ' ') << "Creating BestFirstOpenListFactory as root component..." << endl;
    shared_ptr<BestFirstOpenListFactory> x = create_task_specific_BestFirstOpenListFactory(task, component_map, depth);
    return static_pointer_cast<OpenListFactory>(x);
}


class BestFirstOpenListFeature : public plugins::TypedFeature<TaskIndependentOpenListFactory, TaskIndependentBestFirstOpenListFactory> {
public:
    BestFirstOpenListFeature() : TypedFeature("single") {
        document_title("Best-first open list");
        document_synopsis(
            "Open list that uses a single evaluator and FIFO tiebreaking.");

        add_option<shared_ptr<TaskIndependentEvaluator>>("eval", "evaluator");
        add_option<bool>(
            "pref_only",
            "insert only nodes generated by preferred operators", "false");

        document_note(
            "Implementation Notes",
            "Elements with the same evaluator value are stored in double-ended "
            "queues, called \"buckets\". The open list stores a map from evaluator "
            "values to buckets. Pushing and popping from a bucket runs in constant "
            "time. Therefore, inserting and removing an entry from the open list "
            "takes time O(log(n)), where n is the number of buckets.");
    }
    virtual shared_ptr<TaskIndependentBestFirstOpenListFactory> create_component(const plugins::Options &opts, const utils::Context &context) const override {
        plugins::verify_list_non_empty<shared_ptr<OpenListFactory>>(context, opts, "sublists");
        return make_shared<TaskIndependentBestFirstOpenListFactory>(opts.get<bool>("pref_only"),
                                                                    opts.get<shared_ptr<TaskIndependentEvaluator>>("eval"));
    }
};

static plugins::FeaturePlugin<BestFirstOpenListFeature> _plugin;
}
