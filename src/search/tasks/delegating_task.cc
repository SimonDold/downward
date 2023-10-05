#include "delegating_task.h"

#include "../utils/logging.h"

using namespace std;

namespace tasks {
DelegatingTask::DelegatingTask(const shared_ptr<AbstractTask> &parent)
    : parent(parent) {
}

int DelegatingTask::get_num_variables() const {
    return parent->get_num_variables();
}

string DelegatingTask::get_variable_name(int var) const {
    return parent->get_variable_name(var);
}

int DelegatingTask::get_variable_domain_size(int var) const {
    return parent->get_variable_domain_size(var);
}

int DelegatingTask::get_variable_axiom_layer(int var) const {
    return parent->get_variable_axiom_layer(var);
}

int DelegatingTask::get_variable_default_axiom_value(int var) const {
    return parent->get_variable_default_axiom_value(var);
}

string DelegatingTask::get_fact_name(const FactPair &fact) const {
    return parent->get_fact_name(fact);
}

bool DelegatingTask::are_facts_mutex(const FactPair &fact1, const FactPair &fact2) const {
    return parent->are_facts_mutex(fact1, fact2);
}

int DelegatingTask::get_operator_cost(int index, bool is_axiom) const {
    return parent->get_operator_cost(index, is_axiom);
}

string DelegatingTask::get_operator_name(int index, bool is_axiom) const {
    return parent->get_operator_name(index, is_axiom);
}

int DelegatingTask::get_num_operators() const {
    return parent->get_num_operators();
}

int DelegatingTask::get_num_operator_preconditions(int index, bool is_axiom) const {
    return parent->get_num_operator_preconditions(index, is_axiom);
}

FactPair DelegatingTask::get_operator_precondition(
    int op_index, int fact_index, bool is_axiom) const {
    return parent->get_operator_precondition(op_index, fact_index, is_axiom);
}

int DelegatingTask::get_num_operator_effects(int op_index, bool is_axiom) const {
    return parent->get_num_operator_effects(op_index, is_axiom);
}

int DelegatingTask::get_num_operator_effect_conditions(
    int op_index, int eff_index, bool is_axiom) const {
    return parent->get_num_operator_effect_conditions(op_index, eff_index, is_axiom);
}

FactPair DelegatingTask::get_operator_effect_condition(
    int op_index, int eff_index, int cond_index, bool is_axiom) const {
    return parent->get_operator_effect_condition(op_index, eff_index, cond_index, is_axiom);
}

FactPair DelegatingTask::get_operator_effect(
    int op_index, int eff_index, bool is_axiom) const {
    return parent->get_operator_effect(op_index, eff_index, is_axiom);
}

int DelegatingTask::convert_operator_index(
    int index, const AbstractTask *ancestor_task) const {
    if (ancestor_task == this) {
        return index;
    }
    int parent_index = convert_operator_index_to_parent(index);
    return parent->convert_operator_index(parent_index, ancestor_task);
}

int DelegatingTask::get_num_axioms() const {
    return parent->get_num_axioms();
}

int DelegatingTask::get_num_goals() const {
    return parent->get_num_goals();
}

FactPair DelegatingTask::get_goal_fact(int index) const {
    return parent->get_goal_fact(index);
}

vector<int> DelegatingTask::get_initial_state_values() const {
    return parent->get_initial_state_values();
}

void DelegatingTask::convert_ancestor_state_values(
    vector<int> &values, const AbstractTask *ancestor_task) const {
    if (this == ancestor_task) {
        return;
    }
    parent->convert_ancestor_state_values(values, ancestor_task);
    convert_state_values_from_parent(values);
}


TaskIndependentDelegatingTask::TaskIndependentDelegatingTask() {
}

shared_ptr<DelegatingTask> TaskIndependentDelegatingTask::create_task_specific_DelegatingTask(const shared_ptr<AbstractTask> &task, int depth) {
    utils::g_log << std::string(depth, ' ') << "Creating DelegatingTask as root component..." << endl;
    std::unique_ptr<ComponentMap> component_map = std::make_unique<ComponentMap>();
    return create_task_specific_DelegatingTask(task, component_map, depth);
}

shared_ptr<DelegatingTask> TaskIndependentDelegatingTask::create_task_specific_DelegatingTask(
        [[maybe_unused]] const shared_ptr<AbstractTask> &task,
        [[maybe_unused]] unique_ptr<ComponentMap> &component_map,
        [[maybe_unused]] int depth) {
    cerr << "Tries to create DelegatingTask in an unimplemented way." << endl;
    utils::exit_with(utils::ExitCode::SEARCH_INPUT_ERROR);
}


shared_ptr<AbstractTask> TaskIndependentDelegatingTask::create_task_specific_AbstractTask(const shared_ptr<AbstractTask> &task, unique_ptr<ComponentMap> &component_map, int depth) {
    shared_ptr<DelegatingTask> x = create_task_specific_DelegatingTask(task, component_map, depth);
    return static_pointer_cast<AbstractTask>(x);
}
}
