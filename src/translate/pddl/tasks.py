from typing import List, Union

from . import axioms
from . import predicates
from .actions import Action
from .axioms import Axiom
from .conditions import Atom, Condition
from .f_expression import Assign
from .functions import Function
from .pddl_types import Type, TypedObject
from .predicates import Predicate

class Task:
    def __init__(self, domain_name: str, task_name: str,
                 requirements: "Requirements",
                 types: List[Type], objects: List[TypedObject], predicates:
                 List[Predicate], functions: List[Function],
                 init: List[Union[Atom, Assign]], goal: Condition,
                 actions: List[Action], axioms: List[Axiom],
                 use_metric: int) -> None:
        self.domain_name = domain_name
        self.task_name = task_name
        self.requirements = requirements
        self.types = types
        self.objects = objects
        self.predicates = predicates
        self.functions = functions
        self.init = init
        self.goal = goal
        self.actions = actions
        self.axioms = axioms
        self.axiom_counter = 0
        self.use_max_cost_metric = use_metric

    def add_axiom(self, parameters, condition):
        name = "new-axiom@%d" % self.axiom_counter
        self.axiom_counter += 1
        axiom = axioms.Axiom(name, parameters, len(parameters), condition)
        self.predicates.append(predicates.Predicate(name, parameters))
        self.axioms.append(axiom)
        return axiom

    def dump(self):
        print("Problem %s: %s [%s]" % (
            self.domain_name, self.task_name, self.requirements))
        print("Types:")
        for type in self.types:
            print("  %s" % type)
        print("Objects:")
        for obj in self.objects:
            print("  %s" % obj)
        print("Predicates:")
        for pred in self.predicates:
            print("  %s" % pred)
        print("Functions:")
        for func in self.functions:
            print("  %s" % func)
        print("Init:")
        for fact in self.init:
            print("  %s" % fact)
        print("Goal:")
        self.goal.dump()
        print("Actions:")
        for action in self.actions:
            action.dump()
        if self.axioms:
            print("Axioms:")
            for axiom in self.axioms:
                axiom.dump()


REQUIREMENT_LABELS = [
    ":strips", ":adl", ":typing", ":negation", ":equality",
    ":negative-preconditions", ":disjunctive-preconditions",
    ":existential-preconditions", ":universal-preconditions",
    ":quantified-preconditions", ":conditional-effects",
    ":derived-predicates", ":action-costs"
]


class Requirements:
    def __init__(self, requirements: List[str]):
        self.requirements = requirements
        for req in requirements:
            if req not in REQUIREMENT_LABELS:
                raise ValueError(f"Invalid requirement. Got: {req}\n"
                                 f"Expected: {', '.join(REQUIREMENT_LABELS)}")
    def __str__(self):
        return ", ".join(self.requirements)
