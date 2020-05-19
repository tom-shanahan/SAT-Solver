from helpers import *
from cnf_sat_solver import dpll

# Convert to Conjunctive Normal Form (CNF)
"""
>>> to_cnf_gadget('~(B | C)')
(~B & ~C)
"""
def to_cnf_gadget(s):
    s = expr(s)
    if isinstance(s, str):
        s = expr(s)
    step1 = parse_iff_implies(s)  # Steps 1
    step2 = deMorgansLaw(step1)  # Step 2
    return distibutiveLaw(step2)  # Step 3

# STEP1: if s has IFF or IMPLIES, parse them
def parse_iff_implies(s):
    parsed = expr(s)
    if not parsed.args or is_symbol(parsed.op): # If it is a proposition
        return parsed
    args = list(map(parse_iff_implies, parsed.args)) # recursive parse all args
    a = args[0]
    b = args[-1] # it may have one or more arguments
    if parsed.op == '==>':
        return ~a | b
    elif parsed.op == '<=>':
        return (~a | b) & (~b | a)
    else:
        return Expr(parsed.op, *args)

# STEP2: if there is NOT(~), move it inside, change the operations accordingly.

""" Example:
>>> deMorgansLaw(~(A | B))
(~A & ~B)
"""

def deMorgansLaw(s):
    parsed = expr(s)
    if parsed.op == '~':
        a = parsed.args[0]
        if a.op == '~': # negate inwards
            return deMorgansLaw(a.args[0])
        if a.op == '&':
            ans = []
            for arg in a.args:
                ans.append(deMorgansLaw(~arg)) # negate inwards
            return associate("|", ans) # negate and yields or
        if a.op == '|':
            ans = []
            for arg in a.args:
                ans.append(deMorgansLaw(~arg)) # negate inwards
            return associate("&", list(map(deMorgansLaw, ans))) # negate or yields and
        return s
    elif is_symbol(parsed.op) or not parsed.args:
        return parsed
    else:
        return Expr(parsed.op, *list(map(deMorgansLaw, parsed.args))) # check whether sub args have a negation

# STEP3: use Distibutive Law to distribute and('&') over or('|')

""" Example:
>>> distibutiveLaw((A & B) | C)
((A | C) & (B | C))
"""

def distibutiveLaw(s):
    parsed = expr(s)

    if parsed.op == '|':
        parsed = associate('|', parsed.args)
        and_list = [argument for argument in parsed.args if argument.op == '&'] # find args which is in conjunction form

        if len(and_list) == 0: # if no and can be distributed then return
            return parsed

        other_list = [argument for argument in parsed.args if argument != and_list[0]] # find all other args and ditribute and to them
        other_combined = associate('|', other_list) # combine args
        and_or_list = [distibutiveLaw(argument | other_combined) for argument in and_list[0].args] # distributing and inwards
        and_or_combined = associate('&', and_or_list) # combine all args by and
        return and_or_combined
    elif parsed.op == '&': 
        return associate('&', list(map(distibutiveLaw, parsed.args))) # make sure sub args are in conjunction form
    else: 
        return parsed
    
def SAT_solver(s, heuristic=no_heuristic):
    return dpll(conjuncts(to_cnf_gadget(s)), prop_symbols(s), {}, heuristic)


if __name__ == "__main__":

# Initialization
    A, B, C, D, E, F = expr('A, B, C, D, E, F')
    P, Q, R = expr('P, Q, R')

# Shows alternative ways to write your expression
    assert SAT_solver(A | '<=>' | B) == {A: True, B: True}
    assert SAT_solver(expr('A <=> B')) == {A: True, B: True}

# Some unsatisfiable examples
    assert SAT_solver(P & ~P) is False
    # The whole expression below is essentially just (A&~A)
    assert SAT_solver((A | B | C) & (A | B | ~C) & (A | ~B | C) & (A | ~B | ~C) & (
        ~A | B | C) & (~A | B | ~C) & (~A | ~B | C) & (~A | ~B | ~C)) is False

# This is the same example in the instructions.
    # Notice that SAT_solver's return value  is *Non-deterministic*, and *Non-exhaustive* when the expression is satisfiable,
    # meaning that it will only return *a* satisfying assignment when it succeeds.
    # If you run the same instruction multiple times, you may see different returns, but they should all be satisfying ones.
    result = SAT_solver((~(P | '==>' | Q)) | (R | '==>' | P))
    assert pl_true((~(P | '==>' | Q)) | (R | '==>' | P), result)

    assert pl_true((~(P | '==>' | Q)) | (R | '==>' | P), {P: True})
    assert pl_true((~(P | '==>' | Q)) | (R | '==>' | P), {Q: False, R: False})
    assert pl_true((~(P | '==>' | Q)) | (R | '==>' | P), {R: False})

# Some Boolean expressions has unique satisfying solutions
    assert SAT_solver(A & ~B & C & (A | ~D) & (~E | ~D) & (C | ~D) & (~A | ~F) & (E | ~F) & (~D | ~F) &
                      (B | ~C | D) & (A | ~E | F) & (~A | E | D)) == \
        {B: False, C: True, A: True, F: False, D: True, E: False}
    assert SAT_solver(A & B & ~C & D) == {C: False, A: True, D: True, B: True}
    assert SAT_solver((A | (B & C)) | '<=>' | ((A | B) & (A | C))) == {
        C: True, A: True} or {C: True, B: True}
    assert SAT_solver(A & ~B) == {A: True, B: False}

# The order in which the satisfying variable assignments get returned doen't matter.
    assert {A: True, B: False} == {B: False, A: True}
    print("No assertion errors found so far")
