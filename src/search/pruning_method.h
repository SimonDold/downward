#ifndef PRUNING_METHOD_H
#define PRUNING_METHOD_H

#include "component.h"
#include "operator_id.h"

#include "utils/logging.h"
#include "utils/timer.h"

#include <memory>
#include <vector>

class AbstractTask;
class State;

namespace limited_pruning {
class LimitedPruning;
}

namespace plugins {
class Options;
class Feature;
}

class PruningMethod : public Component {
    utils::Timer timer;
    friend class limited_pruning::LimitedPruning;

    virtual void prune(
        const State &state, std::vector<OperatorID> &op_ids) = 0;
protected:
    mutable utils::LogProxy log;
    std::shared_ptr<AbstractTask> task;
    long num_successors_before_pruning;
    long num_successors_after_pruning;
public:
    explicit PruningMethod(utils::Verbosity verbosity);
    virtual ~PruningMethod() = default;
    virtual void initialize(const std::shared_ptr<AbstractTask> &task);
    void prune_operators(const State &state, std::vector<OperatorID> &op_ids);
    virtual void print_statistics() const;
};

class TaskIndependentPruningMethod : public TaskIndependentComponent<PruningMethod> {
public:
    TaskIndependentPruningMethod(
        const std::string &description,
        utils::Verbosity verbosity);
    virtual ~TaskIndependentPruningMethod();
};

extern void add_pruning_options_to_feature(plugins::Feature &feature, const std::string &description);
extern std::tuple<std::string, utils::Verbosity> get_pruning_arguments_from_options(
    const plugins::Options &opts);

#endif
