#ifndef OPEN_LISTS_PARETO_OPEN_LIST_H
#define OPEN_LISTS_PARETO_OPEN_LIST_H

#include "../open_list_factory.h"

#include "../plugins/options.h"

namespace pareto_open_list {
class ParetoOpenListFactory : public OpenListFactory {
    std::vector<std::shared_ptr<Evaluator>> evals;
    bool pref_only;
    bool state_uniform_selection;
    int random_seed;
public:
    ParetoOpenListFactory(
    std::vector<std::shared_ptr<Evaluator>> evals,
    bool pref_only,
    bool state_uniform_selection,
    int random_seed
            );

    virtual std::unique_ptr<StateOpenList> create_state_open_list() override;
    virtual std::unique_ptr<EdgeOpenList> create_edge_open_list() override;
};
}

#endif
