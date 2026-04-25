"""
CS292C Homework 2 — Problem 1: Z3 Warm-Up + EUF Puzzle (15 points)
===================================================================
Complete each function below. Run this file to check your answers.
"""

from z3 import *


# ---------------------------------------------------------------------------
# Part (a) — 3 pts
# Find integers x, y, z such that x + 2y = z, z > 10, x > 0, y > 0.
# ---------------------------------------------------------------------------
def part_a():
    x, y, z = Ints('x y z')
    s = Solver()

    s.add(x + 2 * y == z)
    s.add(z > 10)
    s.add(x > 0)
    s.add(y > 0)

    print("=== Part (a) ===")
    if s.check() == sat:
        m = s.model()
        print(f"SAT: x={m[x]}, y={m[y]}, z={m[z]}")
    else:
        print("UNSAT (unexpected!)")
    print()


# ---------------------------------------------------------------------------
# Part (b) — 3 pts
# Prove validity of: ∀x. x > 5 → x > 3
# Hint: A formula F is valid iff ¬F is unsatisfiable.
# ---------------------------------------------------------------------------
def part_b():
    x = Int('x')
    s = Solver()

    # Negation of (x > 5 -> x > 3) is (x > 5 AND NOT (x > 3)) = (x > 5 AND x <= 3).
    # If this is UNSAT, the original implication is valid for every integer x.
    s.add(And(x > 5, Not(x > 3)))

    print("=== Part (b) ===")
    result = s.check()
    if result == unsat:
        print("Valid! (negation is UNSAT)")
    else:
        print(f"Not valid — counterexample: {s.model()}")
    print()


# ---------------------------------------------------------------------------
# Part (c) — 5 pts: The EUF Puzzle
#
# Formula:  f(f(x)) = x  ∧  f(f(f(x))) = x  ∧  f(x) ≠ x
#
# STEP 1: Check satisfiability with Z3. (2 pts)
#
# STEP 2: Use Z3 to derive WHY the result holds. (3 pts)
#   Write a series of Z3 validity checks that demonstrate the key reasoning
#   steps. For example, from f(f(x)) = x, what can you derive about f(f(f(x)))?
#   Each check should print what it's testing and whether it holds.
#   Hint: Apply f to both sides of the first equation.
# ---------------------------------------------------------------------------
def part_c():
    S = DeclareSort('S')
    x = Const('x', S)
    f = Function('f', S, S)
    s = Solver()

    s.add(f(f(x)) == x)
    s.add(f(f(f(x))) == x)
    s.add(f(x) != x)

    print("=== Part (c) ===")
    result = s.check()
    if result == sat:
        print(f"SAT: {s.model()}")
    else:
        print("UNSAT")

    # ---- STEP 2: Derivation via Z3 validity checks --------------------------
    # We show UNSAT is forced by three small, independently-valid lemmas over
    # the theory of EUF (equality with uninterpreted functions). For each, we
    # ask Z3 whether (premises ∧ ¬conclusion) is UNSAT; if so the implication
    # is valid. Together these lemmas chain into the contradiction.

    def check_valid(label, premises, conclusion):
        # Validity of (premises -> conclusion) iff (premises ∧ ¬conclusion) UNSAT.
        chk = Solver()
        for p in premises:
            chk.add(p)
        chk.add(Not(conclusion))
        holds = (chk.check() == unsat)
        print(f"  [{'VALID  ' if holds else 'INVALID'}] {label}")

    # Lemma 1: Congruence. Apply f to both sides of f(f(x)) = x to obtain
    # f(f(f(x))) = f(x). This is the key step that bridges the two givens.
    check_valid(
        "f(f(x)) = x  |=  f(f(f(x))) = f(x)     (congruence: apply f to both sides)",
        [f(f(x)) == x],
        f(f(f(x))) == f(x),
    )

    # Lemma 2: Transitivity. Combine Lemma 1's conclusion with the second
    # premise f(f(f(x))) = x to get f(x) = x.
    check_valid(
        "f(f(f(x))) = f(x)  ∧  f(f(f(x))) = x  |=  f(x) = x     (transitivity)",
        [f(f(f(x))) == f(x), f(f(f(x))) == x],
        f(x) == x,
    )

    # Lemma 3: The whole chain. The two original equations imply f(x) = x,
    # which contradicts the third premise f(x) ≠ x — hence the conjunction
    # is UNSAT.
    check_valid(
        "f(f(x)) = x  ∧  f(f(f(x))) = x  |=  f(x) = x     (full derivation)",
        [f(f(x)) == x, f(f(f(x))) == x],
        f(x) == x,
    )
    print()


# ---------------------------------------------------------------------------
# Part (d) — 4 pts: Array Axioms
#
# Prove BOTH axioms (two separate solver checks):
#   (1) Read-over-write HIT:   i = j  →  Select(Store(a, i, v), j) = v
#   (2) Read-over-write MISS:  i ≠ j  →  Select(Store(a, i, v), j) = Select(a, j)
#
# [EXPLAIN] in a comment below: Why are these two axioms together sufficient
# to fully characterize Store/Select behavior? (2–3 sentences)
#
# These two axioms together fully characterize Store/Select because they
# cover every possible index j against a stored index i via the law of
# excluded middle: either j = i (the HIT case, where the read returns the
# just-written value v) or j ≠ i (the MISS case, where the read is
# unaffected and falls through to the prior array). Since every read from
# a Store must fall into exactly one of these two disjoint cases, the pair
# determines the value of Select(Store(a, i, v), j) for every j, which is
# exactly the extensional definition of array update — any model of the
# theory of arrays must agree with this specification everywhere.
# ---------------------------------------------------------------------------
def part_d():
    a = Array('a', IntSort(), IntSort())
    i, j, v = Ints('i j v')

    print("=== Part (d) ===")

    # Axiom 1: Read-over-write HIT.
    # Negate: i = j ∧ Select(Store(a, i, v), j) ≠ v. Expect UNSAT.
    s1 = Solver()
    s1.add(i == j)
    s1.add(Select(Store(a, i, v), j) != v)
    r1 = s1.check()
    print(f"Axiom 1 (hit):  {'Valid' if r1 == unsat else 'INVALID'}")

    # Axiom 2: Read-over-write MISS.
    # Negate: i ≠ j ∧ Select(Store(a, i, v), j) ≠ Select(a, j). Expect UNSAT.
    s2 = Solver()
    s2.add(i != j)
    s2.add(Select(Store(a, i, v), j) != Select(a, j))
    r2 = s2.check()
    print(f"Axiom 2 (miss): {'Valid' if r2 == unsat else 'INVALID'}")
    print()


# ---------------------------------------------------------------------------
if __name__ == "__main__":
    part_a()
    part_b()
    part_c()
    part_d()
