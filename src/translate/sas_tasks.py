from typing import List, Tuple
import math
import re

SAS_FILE_VERSION = 4

DEBUG = False

VarValPair = Tuple[int, int]

def neg(pb_var: str) -> str:
    if pb_var[0] == "~":
        return pb_var[1::]
    else:
        return "~" + pb_var

def implication_from_conjunction_to_disjunction(antecendent_conjuncts: list[str], consequent_disjuncts: list[str]) -> str:
    antecendent = ""
    for conjunct in antecendent_conjuncts:
        antecendent += f" 1 {neg(conjunct)} "
    consequent = ""
    for disjunct in consequent_disjuncts:
        consequent += f" 1 {disjunct} "
    return antecendent + consequent + f" >= 1 ;"

# aka right-reification of conjunction
def implication_from_unit_to_conjunction(antecendent: str, consequent_conjuncts: list[str]) -> str:
    consequent = ""
    for conjunct in consequent_conjuncts:
        consequent += f" 1 {conjunct} "
    return f" {len(consequent_conjuncts)} {neg(antecendent)} " + consequent + f" >= {len(consequent_conjuncts)} ;"

def implication_from_disjunction_to_unit(antecendent_disjuncts: list[str], consequent: str) -> str:
    antecendent = ""
    for disjunct in antecendent_disjuncts:
        antecendent += f" 1 {neg(disjunct)} "
    return f" {len(antecendent_disjuncts)} {consequent} " + antecendent + f" >= {len(antecendent_disjuncts)} ;"



def implication_from_unit_to_disjunction(antecendent: str, consequent_disjuncts: list[str]) -> str:
    return implication_from_conjunction_to_disjunction([antecendent], consequent_disjuncts)


def bi_reification_conjunction(reification_variable: str, conjuncts: list[str]) -> Tuple[str,str]:
    right_reification = implication_from_unit_to_conjunction(reification_variable, conjuncts)
    left_reification = implication_from_unit_to_disjunction(neg(reification_variable), [neg(x) for x in conjuncts] )
    return (left_reification, right_reification)


    


# WARNING: this function has to be syncronized with same named one in the C++ part.
def strips_name_to_veripb_name(strips_name: str) -> str:
        allowed_chars = '[a-zA-Z0-9\\[\\]\\{\\^\\-]'
        pattern = re.compile(allowed_chars)
        veripb_name = ""
        for char in strips_name:
            if not pattern.match(char):
                #veripb_name += f"[ASCII{ord(char)}]"
                veripb_name += "_"
            else:
                veripb_name += char
        return veripb_name

def maplet_name(variable: int, value: int) -> str:
    return f"var_{variable}_{value}"

def axiom_name(axiom_id: int) -> str:
    return f"axiom_{axiom_id}"

def prime_it(name: str) -> str:
    return "prime^" + name

def var_changes_name(variable: int) -> str:
    return f"change_var_{variable}"

def frame_var(variable: int) -> str:
    return f"frame_var_{variable}"

def frame_axiom(variable: int, value: int) -> Tuple[str, str]:
    frame_axiom_pos = f" 1 {neg(frame_var(variable))}  1 {neg(maplet_name(variable, value))}  1 {prime_it(maplet_name(variable, value))}  >= 1"
    frame_axiom_neg = f" 1 {neg(frame_var(variable))}  1 {maplet_name(variable, value)}  1 {neg(prime_it(maplet_name(variable, value)))}  >= 1"
    return frame_axiom_pos, frame_axiom_neg

def operator_implies_frame_axioms(operator_name: str, primary_list: List[int]) -> dict[int, str]:
    frame_axioms = dict()
    for var in primary_list:
        frame_axioms[var] = f" 1 {neg(operator_name)}  1 {frame_var(var)}  >= 1 ;"
    return frame_axioms

def effect_name(operator_name: str, idx: int) -> str:
    return f"{operator_name}_effcond_{idx}"

def weaken_by(constraint: str, variable: str) -> str:
    return f" 1 {variable} " + constraint

def operator_cost_name(cost: int, comperator: str) -> str:
    if comperator == "=":
        return f"delta_cost_eq_{cost}"
    elif comperator == ">=":
        return f"delta_cost_geq_{cost}"
    elif comperator == "<=":
        return f"delta_cost_leq_{cost}"
    else:
        assert(False)
        return "ERROR"

def spent_bit_name(position: int) -> str:
    return f"e_{position}"

def op_name(idx: int) -> str:
    return f"op_{idx}"

def get_delta_meanings(cost: int, primary_variable_count: int, max_cost: int) -> List[str]: 
    delta_eq_rreif = f"2 {neg(operator_cost_name(cost, '='))} 1 {operator_cost_name(cost, '>=')} 1 {operator_cost_name(cost, '<=')} >= 2 ;"
    delta_eq_lreif = f"1 {operator_cost_name(cost, '=')} 1 {neg(operator_cost_name(cost, '>='))} 1 {neg(operator_cost_name(cost, '<='))} >= 1 ;"
    bits = primary_variable_count + math.ceil(math.log(max_cost,2)) # should we cap this to the number of bits FD could handle?
    bits = 4
    maxint = 2**(bits+1) - 1 
    delta_geq_rreif = ""
    delta_geq_lreif = ""
    delta_leq_rreif = ""
    delta_leq_lreif = ""
    pos_prime, neg_normal = "", ""
    neg_prime, pos_normal = "", ""
    for bit in range(0, bits + 1)[::-1]:
        pos_normal += f" {2**bit} {spent_bit_name(bit)} "
        neg_normal += f" {2**bit} {neg(spent_bit_name(bit))} "
        pos_prime += f" {2**bit} {prime_it(spent_bit_name(bit))} "
        neg_prime += f" {2**bit} {neg(prime_it(spent_bit_name(bit)))} "
    delta_geq_rreif = f" {2 * maxint - cost} {neg(operator_cost_name(cost, '>='))} " + pos_prime + neg_normal + f" >= {2 * maxint - cost}"
    delta_geq_lreif = f" {cost + 1} {operator_cost_name(cost, '>=')} " + neg_prime + pos_normal + f" >= {cost + 1}"
    delta_leq_rreif = f" {2 * maxint - (maxint - cost)} {neg(operator_cost_name(cost, '<='))} " + neg_prime + pos_normal + f" >= {2 * maxint - (maxint - cost)}"
    delta_leq_lreif = f" {maxint - cost + 1} {operator_cost_name(cost, '<=')} " + pos_prime + neg_normal + f" >= {maxint - cost + 1}"
    return [delta_eq_rreif, delta_eq_lreif, delta_geq_rreif, delta_geq_lreif, delta_leq_rreif, delta_leq_lreif]


class SASTask:
    """Planning task in finite-domain representation.

    The user is responsible for making sure that the data fits a
    number of structural restrictions. For example, conditions should
    generally be sorted and mention each variable at most once. See
    the validate methods for details."""

    def __init__(self,
                 variables: "SASTask",
                 mutexes: List["SASMutexGroup"],
                 init: "SASInit",
                 goal: "SASGoal",
                 operators: List["SASOperator"],
                 axioms: List["SASAxiom"],
                 metric: bool) -> None:
        self.variables = variables
        self.mutexes = mutexes
        self.init = init
        self.goal = goal
        self.operators = sorted(operators, key=lambda op: (
            op.name, op.prevail, op.pre_post))
        self.axioms = sorted(axioms, key=lambda axiom: (
            axiom.condition, axiom.effect))
        self.metric = metric
        if DEBUG:
            self.validate()

    def validate(self):
        """Fail an assertion if the task is invalid.

        A task is valid if all its components are valid. Valid tasks
        are almost in a kind of "canonical form", but not quite. For
        example, operators and axioms are permitted to be listed in
        any order, even though it would be possible to require some
        kind of canonical sorting.

        Note that we require that all derived variables are binary.
        This is stricter than what later parts of the planner are
        supposed to handle, but some parts of the translator rely on
        this. We might want to consider making this a general
        requirement throughout the planner.

        Note also that there is *no* general rule on what the init (=
        fallback) value of a derived variable is. For example, in
        PSR-Large #1, it can be either 0 or 1. While it is "usually"
        1, code should not rely on this.
        """
        self.variables.validate()
        for mutex in self.mutexes:
            mutex.validate(self.variables)
        self.init.validate(self.variables)
        self.goal.validate(self.variables)
        for op in self.operators:
            op.validate(self.variables)
        for axiom in self.axioms:
            axiom.validate(self.variables, self.init)
        assert self.metric is False or self.metric is True, self.metric

    def dump(self):
        print("variables:")
        self.variables.dump()
        print("%d mutex groups:" % len(self.mutexes))
        for mutex in self.mutexes:
            print("group:")
            mutex.dump()
        print("init:")
        self.init.dump()
        print("goal:")
        self.goal.dump()
        print("%d operators:" % len(self.operators))
        for operator in self.operators:
            operator.dump()
        print("%d axioms:" % len(self.axioms))
        for axiom in self.axioms:
            axiom.dump()
        print("metric: %s" % self.metric)

    def proof_log_init_transition(self) -> List[str]:
        return [] # disjuncts

    def proof_log_update_transition(self, op_name: str, proof_log_object: List[str]) -> List[str]:
            disjuncts = proof_log_object
            disjuncts.append(strips_name_to_veripb_name(op_name))
            return disjuncts

    def proof_log_finalize_transition(self, proof_log_object: List[str]) -> str:
            disjuncts = proof_log_object
            result = "* transition:\n"
            result += implication_from_unit_to_disjunction("transition", disjuncts)
            result += "\n"
            result += implication_from_disjunction_to_unit(disjuncts, "transition")
            return result

    def proof_log_init_axioms(self) -> dict[Tuple[int, int], Tuple[str, str, int]]:
        return dict(), dict()
        # behaviour_constraints # maplet to List[string,string,int]
        # behaviour_prime_constraints

    def proof_log_update_axioms(self, axiom_id, axiom_effect: Tuple[int, int], proof_log_object: Tuple[dict[Tuple[int, int], Tuple[str, str, int]], dict[Tuple[int, int], Tuple[str, str, int]]]) -> Tuple[dict[Tuple[int, int], Tuple[str, str, int]], dict[Tuple[int, int], Tuple[str, str, int]]]:
            behaviour_constraints, behaviour_prime_constraints = proof_log_object
            if not axiom_effect in behaviour_constraints:
                behaviour_constraints[axiom_effect] = ["","", 0]
                behaviour_prime_constraints[axiom_effect] = ["","", 0]
            behaviour_constraints[axiom_effect] = [behaviour_constraints[axiom_effect][0]+f" 1 {axiom_name(axiom_id)} ",
                                                    behaviour_constraints[axiom_effect][1]+f" 1 {neg(axiom_name(axiom_id))} ",
                                                    behaviour_constraints[axiom_effect][2]+1]
            behaviour_prime_constraints[axiom_effect] = [behaviour_prime_constraints[axiom_effect][0]+f" 1 {axiom_name(axiom_id)} ",
                                                    behaviour_prime_constraints[axiom_effect][1]+f" 1 {neg(axiom_name(axiom_id))} ",
                                                    behaviour_prime_constraints[axiom_effect][2]+1]
            return behaviour_constraints, behaviour_prime_constraints

    def proof_log_finalize_axioms(self, proof_log_object: Tuple[dict[Tuple[int, int], Tuple[str, str, int]], dict[Tuple[int, int], Tuple[str, str, int]]]) -> str:
            behaviour_constraints, behaviour_prime_constraints = proof_log_object
            result = "\n* axioms\n"
            result_prime = "\n\n* axiom Prime\n"
            for (var, val) in behaviour_constraints:
                result += behaviour_constraints[(var, val)][0] + \
                    f" 1 {neg(maplet_name(var, val))}  >=  1\n" + \
                    behaviour_constraints[(var, val)][1] + \
                    f" {behaviour_constraints[(var, val)][2]} {maplet_name(var, val)} " + \
                    f" >=  {behaviour_constraints[(var, val)][2]}\n"
                result_prime += behaviour_prime_constraints[(var, val)][0] + \
                    f" 1 {neg(prime_it(maplet_name(var, val)))}  >=  1\n" + \
                    behaviour_prime_constraints[(var, val)][1] + \
                    f" {behaviour_prime_constraints[(var, val)][2]} {prime_it(maplet_name(var, val))} " + \
                    f" >=  {behaviour_prime_constraints[(var, val)][2]}\n"

            return result + result_prime


    def output(self, sas_stream, opb_stream=None):
        print("begin_version", file=sas_stream)
        print("* PB-encoding of task:", file=opb_stream)
        print(SAS_FILE_VERSION, file=sas_stream)
        print("end_version", file=sas_stream)
        print("begin_metric", file=sas_stream)
        print(int(self.metric), file=sas_stream)
        print("end_metric", file=sas_stream)
        layer_dict, primary_list = self.variables.output(sas_stream, opb_stream)
        print(len(self.mutexes), file=sas_stream)
        for mutex in self.mutexes:
            mutex.output(sas_stream)
        print("\n* ignoring mutex groups", file=opb_stream)
        self.init.output(sas_stream, opb_stream)
        self.goal.output(sas_stream, opb_stream)
        print(len(self.operators), file=sas_stream)
        proof_log_object_transition = self.proof_log_init_transition()
        for op_id, op in enumerate(self.operators):
            op.output(sas_stream, op_id, primary_list, max(self.metric, 1), opb_stream)
            proof_log_object_transition = self.proof_log_update_transition(op_name(op_id), proof_log_object_transition)
        print(self.proof_log_finalize_transition(proof_log_object_transition), file=opb_stream)
        print(len(self.axioms), file=sas_stream)
        proof_log_object_axioms = self.proof_log_init_axioms()
        for i, axiom in enumerate(self.axioms):
            axiom.output(sas_stream, i, opb_stream)
            proof_log_object_axioms = self.proof_log_update_axioms(i, axiom.effect, proof_log_object_axioms)
        print(self.proof_log_finalize_axioms(proof_log_object_axioms), file=opb_stream)
        



    def get_encoding_size(self):
        task_size = 0
        task_size += self.variables.get_encoding_size()
        for mutex in self.mutexes:
            task_size += mutex.get_encoding_size()
        task_size += self.goal.get_encoding_size()
        for op in self.operators:
            task_size += op.get_encoding_size()
        for axiom in self.axioms:
            task_size += axiom.get_encoding_size()
        return task_size


class SASVariables:
    def __init__(self, ranges: List[int], axiom_layers: List[int],
                 value_names: List[List[str]]) -> None:
        self.ranges = ranges
        self.axiom_layers = axiom_layers
        self.value_names = value_names

    def validate(self):
        """Validate variables.

        All variables must have range at least 2, and derived
        variables must have range exactly 2. See comment on derived
        variables in the docstring of SASTask.validate.
        """
        assert len(self.ranges) == len(self.axiom_layers) == len(
            self.value_names)
        for (var_range, layer, var_value_names) in zip(
                self.ranges, self.axiom_layers, self.value_names):
            assert var_range == len(var_value_names)
            assert var_range >= 2
            assert layer == -1 or layer >= 0
            if layer != -1:
                assert var_range == 2

    def validate_fact(self, fact):
        """Assert that fact is a valid (var, value) pair."""
        var, value = fact
        assert 0 <= var < len(self.ranges)
        assert 0 <= value < self.ranges[var]

    def validate_condition(self, condition):
        """Assert that the condition (list of facts) is sorted, mentions each
        variable at most once, and only consists of valid facts."""
        last_var = -1
        for (var, value) in condition:
            self.validate_fact((var, value))
            assert var > last_var
            last_var = var

    def dump(self):
        for var, (rang, axiom_layer) in enumerate(
                zip(self.ranges, self.axiom_layers)):
            if axiom_layer != -1:
                axiom_str = " [axiom layer %d]" % axiom_layer
            else:
                axiom_str = ""
            print("v%d in {%s}%s" % (var, list(range(rang)), axiom_str))

    def proof_log_var_init(self, var: int) -> Tuple[str,str,str,str,str]:
        #frame_axioms, var_domain_max_one, var_domain_min_one, var_prime_domain_max_one, var_prime_domain_min_one
        return ("", f"@dom_{var}_max_one ", f"@dom_{var}_min_one ", "", "") 
    
    def proof_log_var_update(self, var: str, i: int, axiom_layer: int, x: Tuple[str,str,str,str,str]) -> Tuple[str,str,str,str,str]:
        (frame_axioms, var_domain_max_one, var_domain_min_one, var_prime_domain_max_one, var_prime_domain_min_one) = x
        var_domain_max_one += f"1 {neg(maplet_name(var,i))} "
        var_domain_min_one += f"1 {maplet_name(var,i)} "
        var_prime_domain_max_one += f"1 {neg(prime_it(maplet_name(var,i)))} "
        var_prime_domain_min_one += f"1 {prime_it(maplet_name(var,i))} "
        if axiom_layer == -1:
            frame_axiom_pos, frame_axiom_neg = frame_axiom(var,i)
            frame_axioms += frame_axiom_pos + "\n" + frame_axiom_neg + "\n"
        return (frame_axioms, var_domain_max_one, var_domain_min_one, var_prime_domain_max_one, var_prime_domain_min_one)
        
    def proof_log_var_finalize(self, length: int, x: Tuple[str,str,str,str,str]) -> str:
        (frame_axioms, var_domain_max_one, var_domain_min_one, var_prime_domain_max_one, var_prime_domain_min_one) = x
        var_domain_max_one = var_domain_max_one + f">= {length-1} ;"
        var_domain_min_one = var_domain_min_one + ">= 1 ;"
        var_prime_domain_max_one = var_prime_domain_max_one + f">= {length-1} ;"
        var_prime_domain_min_one = var_prime_domain_min_one + ">= 1 ;"
        var_domain_constraints = var_domain_max_one + "\n" + var_domain_min_one + "\n" + var_prime_domain_max_one + "\n" + var_prime_domain_min_one + "\n" + frame_axioms
        return var_domain_constraints

    def output(self, sas_stream, opb_stream=None):
        print(len(self.ranges), file=sas_stream)
        layer_dict = dict()
        primary_list = []
        for var, (rang, axiom_layer, values) in enumerate(zip(
                self.ranges, self.axiom_layers, self.value_names)):
            print("begin_variable", file=sas_stream)
            print("var%d" % var, file=sas_stream)
            print(axiom_layer, file=sas_stream)
            layer_dict[var] = axiom_layer
            if axiom_layer == -1:
                primary_list += [var]
            print(rang, file=sas_stream)
            assert rang == len(values), (rang, values)
            proof_log_object = self.proof_log_var_init(var)
            for i, value in enumerate(values):
                print(value, file=sas_stream)
                proof_log_object = self.proof_log_var_update(var, i, axiom_layer, proof_log_object)
            print(("* var%d domain constraints \n" %var) + self.proof_log_var_finalize(len(values), proof_log_object), file=opb_stream)
            print("end_variable", file=sas_stream)
        return layer_dict, primary_list

    def get_encoding_size(self):
        # A variable with range k has encoding size k + 1 to also give the
        # variable itself some weight.
        return len(self.ranges) + sum(self.ranges)


class SASMutexGroup:
    def __init__(self, facts: List[VarValPair]):
        self.facts = sorted(facts)

    def validate(self, variables):
        """Assert that the facts in the mutex group are sorted and unique
        and that they are all valid."""
        for fact in self.facts:
            variables.validate_fact(fact)
        assert self.facts == sorted(set(self.facts))

    def dump(self):
        for var, val in self.facts:
            print("v%d: %d" % (var, val))

    def output(self, sas_stream, opb_stream=None):
        print("begin_mutex_group", file=sas_stream)
        print(len(self.facts), file=sas_stream)
        for var, val in self.facts:
            print(var, val, file=sas_stream)
        print("end_mutex_group", file=sas_stream)

    def get_encoding_size(self):
        return len(self.facts)


class SASInit:
    def __init__(self, values):
        self.values = values

    def validate(self, variables):
        """Validate initial state.

        Assert that the initial state contains the correct number of
        values and that all values are in range.
        """

        assert len(self.values) == len(variables.ranges)
        for fact in enumerate(self.values):
            variables.validate_fact(fact)

    def dump(self):
        for var, val in enumerate(self.values):
            print("v%d: %d" % (var, val))

    def proof_log_init(self) -> List[str]:
        return [] # conjuncts

    def proof_log_update(self, i: int, val: str, conjuncts: List[str]) -> List[str]:
        conjuncts.append(maplet_name(i,val))
        return conjuncts
    
    def proof_log_finalize(self, conjuncts: List[str]) -> str:
        state_name = "s_init"
        left_reification, right_reification = bi_reification_conjunction(state_name, conjuncts)
        state_reification = "\n* init state reification:\n" + right_reification + "\n" + left_reification
        return state_reification

    def output(self, sas_stream, opb_stream=None):
        print("begin_state", file=sas_stream)
        proof_log_object = self.proof_log_init()
        for i, val in enumerate(self.values):
            print(val, file=sas_stream)
            proof_log_object = self.proof_log_update(i, val, proof_log_object)
        print(self.proof_log_finalize(proof_log_object), file=opb_stream)
        print("end_state", file=sas_stream)


class SASGoal:
    def __init__(self, pairs: List[Tuple[int, int]]) -> None:
        self.pairs = sorted(pairs)

    def validate(self, variables):
        """Assert that the goal is nonempty and a valid condition."""
        assert self.pairs
        variables.validate_condition(self.pairs)

    def dump(self):
        for var, val in self.pairs:
            print("v%d: %d" % (var, val))

    def proof_log_init(self) -> List[str]:
        return [] # conjuncts

    def proof_log_update(self, var: str, val: str, conjuncts: List[str]) -> List[str]:
        conjuncts.append(maplet_name(var,val))
        return conjuncts
    
    def proof_log_finalize(self, conjuncts: List[str]) -> str:
        partial_state_name = "goal"
        left_reification, right_reification = bi_reification_conjunction(partial_state_name, conjuncts)
        partial_state_reification = "\n* goal condition reification:\n" + right_reification + "\n" + left_reification
        return partial_state_reification

    def output(self, sas_stream, opb_stream=None):
        print("begin_goal", file=sas_stream)
        print(len(self.pairs), file=sas_stream)
        proof_log_object = self.proof_log_init()
        for var, val in self.pairs:
            print(var, val, file=sas_stream)
            proof_log_object = self.proof_log_update(var, val, proof_log_object)
        print(self.proof_log_finalize(proof_log_object), file=opb_stream)
        print("end_goal", file=sas_stream)

    def get_encoding_size(self):
        return len(self.pairs)


class SASOperator:
    def __init__(self, name: str, prevail: List[VarValPair], pre_post:
            List[Tuple[int, int, int, List[VarValPair]]], cost: int) -> None:
        self.name = name
        self.prevail = sorted(prevail)
        self.pre_post = self._canonical_pre_post(pre_post)
        self.cost = cost

    def _canonical_pre_post(self, pre_post):
        # Return a sorted and uniquified version of pre_post. We would
        # like to just use sorted(set(pre_post)), but this fails because
        # the effect conditions are a list and hence not hashable.
        def tuplify(entry):
            var, pre, post, cond = entry
            return var, pre, post, tuple(cond)
        def listify(entry):
            var, pre, post, cond = entry
            return var, pre, post, list(cond)
        pre_post = map(tuplify, pre_post)
        pre_post = sorted(set(pre_post))
        pre_post = list(map(listify, pre_post))
        return pre_post

    def validate(self, variables):
        """Validate the operator.

        Assert that
        1. Prevail conditions are valid conditions (i.e., sorted and
           all referring to different variables)
        2. The pre_post list is sorted by (var, pre, post, cond), and the
           same (var, pre, post, cond) 4-tuple is not repeated.
        3. Effect conditions are valid conditions and do not contain variables
           from the pre- or prevail conditions.
        4. Variables occurring in pre_post rules do not have a prevail
           condition.
        5. Preconditions in pre_post are -1 or valid facts.
        6. Effects are valid facts.
        7. Effect variables are non-derived.
        8. If a variable has multiple pre_post rules, then pre is
           identical in all these rules.
        9. There is at least one effect.
        10. Costs are non-negative integers.

        Odd things that are *not* illegal:
        - The effect in a pre_post rule may be identical to the
          precondition or to an effect condition of that effect.

        TODO/open question:
        - It is currently not very clear what the semantics of operators
          should be when effects "conflict", i.e., when multiple effects
          trigger and want to set a given variable to two different
          values. In the case where both are unconditional effects, we
          should make sure that our representation doesn't actually
          contain two such effects, but when at least one of them is
          conditional, things are not so easy.

          To make our life simpler when generating SAS+ tasks from
          PDDL tasks, it probably makes most sense to generalize the
          PDDL rule in this case: there is a value order where certain
          values "win" over others in this situation. It probably
          makes sense to say the "highest" values should win in this
          case, because that's consistent with the PDDL rules if we
          say false = 0 and true = 1, and also with our sort order of
          effects it means we get the right result if we just apply
          effects in sequence.

          But whatever we end up deciding, we need to be clear about it,
          document it and make sure that all of our code knows the rules
          and follows them.
        """

        variables.validate_condition(self.prevail)
        assert self.pre_post == self._canonical_pre_post(self.pre_post)
        prevail_vars = {var for (var, value) in self.prevail}
        pre_values = {}
        for var, pre, post, cond in self.pre_post:
            variables.validate_condition(cond)
            assert var not in prevail_vars
            if pre != -1:
                variables.validate_fact((var, pre))
            variables.validate_fact((var, post))
            assert variables.axiom_layers[var] == -1
            if var in pre_values:
                assert pre_values[var] == pre
            else:
                pre_values[var] = pre
        for var, pre, post, cond in self.pre_post:
            for cvar, cval in cond:
                assert cvar not in pre_values or pre_values[cvar] == -1
                assert cvar not in prevail_vars
        assert self.pre_post
        assert self.cost >= 0 and self.cost == int(self.cost)

    def dump(self):
        print(self.name)
        print("Prevail:")
        for var, val in self.prevail:
            print("  v%d: %d" % (var, val))
        print("Pre/Post:")
        for var, pre, post, cond in self.pre_post:
            if cond:
                cond_str = " [%s]" % ", ".join(
                    ["%d: %d" % tuple(c) for c in cond])
            else:
                cond_str = ""
            print("  v%d: %d -> %d%s" % (var, pre, post, cond_str))

    def proof_log_init_prevail(self) -> List[str]:
        return [] # prevail_conjuncts

    def proof_log_update_prevail(self, var: str, val: str, prevail_conjuncts: List[str]) -> List[str]:
        prevail_conjuncts.append(maplet_name(var,val))
        return prevail_conjuncts

    def proof_log_init(self, op_id, primary_list: List[int]) -> Tuple[str, dict[int, str], List[str], List[str], List[str]]:
        operator_name = op_name(op_id)
        frame_axioms = operator_implies_frame_axioms(operator_name, primary_list)
        postconditions = []
        preconditions = []
        reifications_of_postcondition_antecedent_conjuncts = []
        return (operator_name, frame_axioms, postconditions, preconditions, reifications_of_postcondition_antecedent_conjuncts)

    def proof_log_init_inner(self) -> List[str]:
        return [] # postcondition_antecedent_conjuncts

    def proof_log_update_inner(self, cvar: int, cval: int, postcondition_antecedent_conjuncts: List[str]) -> List[str]:
        postcondition_antecedent_conjuncts.append(maplet_name(cvar,cval))
        return postcondition_antecedent_conjuncts

    def proof_log_update(self, i: int, var: int, pre: int,  post: int, proof_log_object_inner: List[str], proof_log_object: Tuple[str, dict[int, str], List[str], List[str], List[str]]) -> Tuple[str, dict[int, str], List[str], List[str], List[str]]:
        postcondition_antecedent_conjuncts = proof_log_object_inner
        (operator_name, frame_axioms, postconditions, preconditions, reifications_of_postcondition_antecedent_conjuncts) = proof_log_object
        postcondition = implication_from_conjunction_to_disjunction([operator_name, effect_name(operator_name, i)], [prime_it(maplet_name(var,post))])
        left_reification_of_postcondition_antecedent_conjuncts, right_reification_of_postcondition_antecedent_conjuncts = bi_reification_conjunction(effect_name(operator_name, i), postcondition_antecedent_conjuncts)
        reifications_of_postcondition_antecedent_conjuncts.append(left_reification_of_postcondition_antecedent_conjuncts)
        reifications_of_postcondition_antecedent_conjuncts.append(right_reification_of_postcondition_antecedent_conjuncts)
        postconditions.append(postcondition)
        if not pre == -1:
            preconditions.append(maplet_name(var,pre))
        frame_axioms[var] = weaken_by(frame_axioms[var], effect_name(operator_name, i))
        return (operator_name, frame_axioms, postconditions, preconditions, reifications_of_postcondition_antecedent_conjuncts)
    
    def proof_log_finalize(self, primary_variable_count: int, max_cost: int, prevail_conjuncts: List[str], proof_log_object: Tuple[str, dict[int, str], List[str], List[str], List[str]]) -> str:
        (operator_name, frame_axioms, postconditions, preconditions, reifications_of_postcondition_antecedent_conjuncts) = proof_log_object
        operator_implies_preconditions_and_prevail_conditions = implication_from_unit_to_conjunction(operator_name, prevail_conjuncts + preconditions)
        operator_reification = f"\n* operator '{self.name[1:-1]}' aka '{strips_name_to_veripb_name(self.name[1:-1])}' reification:\n"
        cost = implication_from_unit_to_conjunction(operator_name, [operator_cost_name(self.cost, '=')])
        delat_meanings = get_delta_meanings(self.cost, primary_variable_count, max_cost)
        for x in ["* op implies pre:"] + [operator_implies_preconditions_and_prevail_conditions] + ["* post:"] + postconditions + ["* weak frame:"] + [frame_axioms[fa] for fa in frame_axioms] + ["* effect conditions:"] + reifications_of_postcondition_antecedent_conjuncts + ["* cost"] + [cost] + delat_meanings:
            operator_reification += x + "\n"
        return operator_reification

    def output(self, sas_stream, op_id, primary_list, max_cost, opb_stream=None):
        print("begin_operator", file=sas_stream)
        print(self.name[1:-1], file=sas_stream)
        
        print(len(self.prevail), file=sas_stream)
        proof_log_object_prevail = self.proof_log_init_prevail()
        for var, val in self.prevail:
            proof_log_object_prevail = self.proof_log_update_prevail(var, val, proof_log_object_prevail)
            print(var, val, file=sas_stream)
        print(len(self.pre_post), file=sas_stream)

        proof_log_object = self.proof_log_init(op_id, primary_list)
        for i, (var, pre, post, cond) in enumerate(self.pre_post):
            print(len(cond), end=' ', file=sas_stream)
            proof_log_object_inner = self.proof_log_init_inner()
            for cvar, cval in cond:
                proof_log_object_inner = self.proof_log_update_inner(cvar, cval, proof_log_object_inner)
                print(cvar, cval, end=' ', file=sas_stream)
            proof_log_object = self.proof_log_update(i, var, pre, post, proof_log_object_inner, proof_log_object)
            print(var, pre, post, file=sas_stream)
        #   
        print(self.proof_log_finalize(len(primary_list), max_cost, proof_log_object_prevail, proof_log_object), file=opb_stream)
        print(self.cost, file=sas_stream)
        print("end_operator", file=sas_stream)

    def get_encoding_size(self):
        size = 1 + len(self.prevail)
        for var, pre, post, cond in self.pre_post:
            size += 1 + len(cond)
            if pre != -1:
                size += 1
        return size

    def get_applicability_conditions(self):
        """Return the combined applicability conditions
        (prevail conditions and preconditions) of the operator.

        Returns a sorted list of (var, value) pairs. This is
        guaranteed to contain at most one fact per variable and
        must hence be non-contradictory."""
        conditions = {}
        for var, val in self.prevail:
            assert var not in conditions
            conditions[var] = val
        for var, pre, post, cond in self.pre_post:
            if pre != -1:
                assert var not in conditions or conditions[var] == pre
                conditions[var] = pre
        return sorted(conditions.items())


class SASAxiom:
    def __init__(self, condition: List[VarValPair], effect: VarValPair) -> None:
        self.condition = sorted(condition)
        self.effect = effect
        assert self.effect[1] in (0, 1)

        for _, val in condition:
            assert val >= 0, condition

    def validate(self, variables, init):

        """Validate the axiom.

        Assert that the axiom condition is a valid condition, that the
        effect is a valid fact, that the effect variable is a derived
        variable, and that the layering condition is satisfied.

        See the docstring of SASTask.validate for information on the
        restriction on derived variables. The layering condition boils
        down to:

        1. Axioms always set the "non-init" value of the derived
           variable.
        2. Derived variables in the condition must have a lower of
           equal layer to derived variables appearing in the effect.
        3. Conditions with equal layer are only allowed when the
           condition uses the "non-init" value of that variable.

        TODO/bug: rule #1 is currently disabled because we currently
        have axioms that violate it. This is likely due to the
        "extended domain transition graphs" described in the Fast
        Downward paper, Section 5.1. However, we want to eventually
        changes this. See issue454. For cases where rule #1 is violated,
        "non-init" should be "init" in rule #3.
        """

        variables.validate_condition(self.condition)
        variables.validate_fact(self.effect)
        eff_var, eff_value = self.effect
        eff_layer = variables.axiom_layers[eff_var]
        assert eff_layer >= 0
        eff_init_value = init.values[eff_var]
        ## The following rule is currently commented out because of
        ## the TODO/bug mentioned in the docstring.
        # assert eff_value != eff_init_value
        for cond_var, cond_value in self.condition:
            cond_layer = variables.axiom_layers[cond_var]
            if cond_layer != -1:
                assert cond_layer <= eff_layer
                if cond_layer == eff_layer:
                    cond_init_value = init.values[cond_var]
                    ## Once the TODO/bug above is addressed, the
                    ## following four lines can be simplified because
                    ## we are guaranteed to land in the "if" branch.
                    if eff_value != eff_init_value:
                        assert cond_value != cond_init_value
                    else:
                        assert cond_value == cond_init_value

    def dump(self):
        print("Condition:")
        for var, val in self.condition:
            print("  v%d: %d" % (var, val))
        print("Effect:")
        var, val = self.effect
        print("  v%d: %d" % (var, val))

    def proof_log_init(self) -> Tuple[str,str,str,str]:
        return "","","","" #fire_constraint_Lreif, fire_constraint_Rreif, fire_constraint_prime_Lreif, fire_constraint_prime_Rreif

    def proof_log_update(self, var: int, val: int, proof_log_object: Tuple[str,str,str,str]) -> Tuple[str,str,str,str]:
        fire_constraint_Lreif, fire_constraint_Rreif, fire_constraint_prime_Lreif, fire_constraint_prime_Rreif = proof_log_object

        fire_constraint_Lreif += f" 1 {neg(maplet_name(var, val))} "
        fire_constraint_Rreif += f" 1 {maplet_name(var, val)}"
        fire_constraint_prime_Lreif += f" 1 {neg(prime_it(maplet_name(var, val)))} "
        fire_constraint_prime_Rreif += f" 1 {prime_it(maplet_name(var, val))}"

        return fire_constraint_Lreif, fire_constraint_Rreif, fire_constraint_prime_Lreif, fire_constraint_prime_Rreif

    def proof_log_finalize(self, condition_length: int, axiom_id: int, proof_log_object: Tuple[str, str, str, str]) -> str:
        fire_constraint_Lreif, fire_constraint_Rreif, fire_constraint_prime_Lreif, fire_constraint_prime_Rreif = proof_log_object

        fire_constraint_Lreif += f" 1 {axiom_name(axiom_id)}  >=  1"
        fire_constraint_Rreif += f" {condition_length} {neg(axiom_name(axiom_id))}  >=  {condition_length}\n"
        fire_constraint_prime_Lreif += f" 1 {prime_it(axiom_name(axiom_id))}  >=  1"
        fire_constraint_prime_Rreif += f" {condition_length} {neg(prime_it(axiom_name(axiom_id)))}  >=  {condition_length}\n"

        return fire_constraint_Lreif + "\n" + fire_constraint_Rreif + "\n" + fire_constraint_prime_Lreif + "\n" + fire_constraint_prime_Rreif

    def output(self, sas_stream, axiom_id, opb_stream=None):
        print("begin_rule", file=sas_stream)
        print(len(self.condition), file=sas_stream)
        proof_log_object = self.proof_log_init()
        for var, val in self.condition:
            print(var, val, file=sas_stream)
            proof_log_object = self.proof_log_update(var, val, proof_log_object)
        var, val = self.effect
        print(self.proof_log_finalize(len(self.condition), axiom_id, proof_log_object), file=opb_stream)
        print(var, 1 - val, val, file=sas_stream)
        print("end_rule", file=sas_stream)

    def get_encoding_size(self):
        return 1 + len(self.condition)
