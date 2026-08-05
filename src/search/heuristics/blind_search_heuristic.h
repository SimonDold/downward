#ifndef HEURISTICS_BLIND_SEARCH_HEURISTIC_H
#define HEURISTICS_BLIND_SEARCH_HEURISTIC_H

#include "../heuristic.h"

namespace blind_search_heuristic {
class BlindSearchHeuristic : public Heuristic {
    int min_operator_cost;
protected:
    void certify_heuristic_blind(int return_value, State ancestor_state, std::string comment = "certify_heuristic_blind");
    virtual int compute_heuristic(const State &ancestor_state) override;
public:
    BlindSearchHeuristic(
        const std::shared_ptr<AbstractTask> &transform,
        bool cache_estimates, const std::string &description,
        utils::Verbosity verbosity);
};
}

#endif
