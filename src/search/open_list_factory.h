#ifndef OPEN_LIST_FACTORY_H
#define OPEN_LIST_FACTORY_H

#include "component.h"
#include "open_list.h"

#include "plugins/plugin.h"

#include <memory>


class OpenListFactory : public Component {
public:
    OpenListFactory() = default;
    virtual ~OpenListFactory() = default;

    OpenListFactory(const OpenListFactory &) = delete;

    virtual std::unique_ptr<StateOpenList> create_state_open_list() = 0;
    virtual std::unique_ptr<EdgeOpenList> create_edge_open_list() = 0;

    /*
      The following template receives manual specializations (in the
      cc file) for the open list types we want to support. It is
      intended for templatized callers, e.g. the constructor of
      AlternationOpenList.
    */
    template<typename T>
    std::unique_ptr<OpenList<T>> create_open_list();
};


class TaskIndependentOpenListFactory : public TaskIndependentComponent<OpenListFactory> {
public:
    TaskIndependentOpenListFactory(const std::string &description, utils::Verbosity verbosity);
    virtual ~TaskIndependentOpenListFactory() = default;

    TaskIndependentOpenListFactory(const TaskIndependentOpenListFactory &) = delete;

};

extern void add_open_list_options_to_feature(
    plugins::Feature &feature);
extern std::tuple<bool>
get_open_list_arguments_from_options(const plugins::Options &opts);
#endif
