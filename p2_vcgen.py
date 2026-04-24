"""
CS292C Homework 2 — Problem 2: Hoare Logic VCG for IMP (30 points)
===================================================================
Implement weakest-precondition-based verification condition generation
for a simple IMP language, using Z3 to discharge the VCs.

Part (a): Compute wp using your VCG and analyze preconditions with Z3.
          NOTE: Part (a) depends on Part (b). Implement Part (b) first, then come back to Part (a).
Part (b): Implement wp() and verify() below.
Part (c): Discover loop invariants for three programs.
Part (d): Find and fix a bug in a provided invariant.
"""

from z3 import *
from dataclasses import dataclass
from typing import Union

# ============================================================================
# IMP Abstract Syntax Tree
# ============================================================================

@dataclass
class IntConst:
    value: int

@dataclass
class Var:
    name: str

@dataclass
class BinOp:
    """op ∈ {'+', '-', '*'}"""
    op: str
    left: 'AExp'
    right: 'AExp'

AExp = Union[IntConst, Var, BinOp]

@dataclass
class BoolConst:
    value: bool

@dataclass
class Compare:
    """op ∈ {'<', '<=', '>', '>=', '==', '!='}"""
    op: str
    left: AExp
    right: AExp

@dataclass
class ImpNot:
    expr: 'BExp'

@dataclass
class ImpAnd:
    left: 'BExp'
    right: 'BExp'

@dataclass
class ImpOr:
    left: 'BExp'
    right: 'BExp'

BExp = Union[BoolConst, Compare, ImpNot, ImpAnd, ImpOr]

@dataclass
class Assign:
    var: str
    expr: AExp

@dataclass
class Seq:
    s1: 'Stmt'
    s2: 'Stmt'

@dataclass
class If:
    cond: BExp
    then_branch: 'Stmt'
    else_branch: 'Stmt'

@dataclass
class While:
    cond: BExp
    invariant: 'BExp'
    body: 'Stmt'

@dataclass
class Assert:
    cond: BExp

@dataclass
class Assume:
    cond: BExp

Stmt = Union[Assign, Seq, If, While, Assert, Assume]

# ============================================================================
# IMP AST → Z3 Translation
# ============================================================================

_z3_vars: dict[str, ArithRef] = {}

def z3_var(name: str) -> ArithRef:
    if name not in _z3_vars:
        _z3_vars[name] = Int(name)
    return _z3_vars[name]

def aexp_to_z3(e: AExp) -> ArithRef:
    match e:
        case IntConst(v):   return IntVal(v)
        case Var(name):     return z3_var(name)
        case BinOp('+', l, r): return aexp_to_z3(l) + aexp_to_z3(r)
        case BinOp('-', l, r): return aexp_to_z3(l) - aexp_to_z3(r)
        case BinOp('*', l, r): return aexp_to_z3(l) * aexp_to_z3(r)
        case _: raise ValueError(f"Unknown AExp: {e}")

def bexp_to_z3(e: BExp) -> BoolRef:
    match e:
        case BoolConst(v):   return BoolVal(v)
        case Compare(op, l, r):
            lz, rz = aexp_to_z3(l), aexp_to_z3(r)
            return {'<': lz < rz, '<=': lz <= rz, '>': lz > rz,
                    '>=': lz >= rz, '==': lz == rz, '!=': lz != rz}[op]
        case ImpNot(inner):  return z3.Not(bexp_to_z3(inner))
        case ImpAnd(l, r):   return z3.And(bexp_to_z3(l), bexp_to_z3(r))
        case ImpOr(l, r):    return z3.Or(bexp_to_z3(l), bexp_to_z3(r))
        case _: raise ValueError(f"Unknown BExp: {e}")

def z3_substitute_var(formula: ExprRef, var_name: str, replacement: ArithRef) -> ExprRef:
    """Replace every occurrence of z3 variable `var_name` with `replacement`."""
    return substitute(formula, (z3_var(var_name), replacement))


# ============================================================================
# Part (b): Weakest Precondition + VCG — 12 pts
# ============================================================================

side_vcs: list[tuple[str, BoolRef]] = []

def wp(stmt: Stmt, Q: BoolRef) -> BoolRef:
    """
    Compute the weakest precondition of `stmt` w.r.t. postcondition `Q`.
    For while loops, append side VCs to the global `side_vcs` list.

    TODO: Implement all six cases.
    """
    global side_vcs

    match stmt:
        case Assign(var, expr):
            return z3_substitute_var(Q, var, aexp_to_z3(expr))

        case Seq(s1, s2):
            return wp(s1, wp(s2, Q))

        case If(cond, s1, s2):
            b = bexp_to_z3(cond)
            return z3.And(z3.Implies(b, wp(s1, Q)),
                          z3.Implies(z3.Not(b), wp(s2, Q)))

        case While(cond, inv, body):
            I = bexp_to_z3(inv)
            b = bexp_to_z3(cond)
            side_vcs.append(("preservation", z3.Implies(z3.And(I, b), wp(body, I))))
            side_vcs.append(("postcondition", z3.Implies(z3.And(I, z3.Not(b)), Q)))
            return I

        case Assert(cond):
            return z3.And(bexp_to_z3(cond), Q)

        case Assume(cond):
            return z3.Implies(bexp_to_z3(cond), Q)

        case _:
            raise ValueError(f"Unknown statement: {stmt}")


def verify(pre: BExp, stmt: Stmt, post: BExp, label: str = "Program"):
    """
    Verify the Hoare triple {pre} stmt {post}.
    1. Clear side_vcs.  2. Compute wp.  3. Check pre → wp is valid.
    4. Check each side VC.  5. Print results.

    TODO: Implement this function.
    """
    global side_vcs
    side_vcs = []

    pre_z3 = bexp_to_z3(pre)
    post_z3 = bexp_to_z3(post)

    wp_result = wp(stmt, post_z3)

    print(f"=== {label} ===")

    all_ok = True

    s = Solver()
    s.add(z3.Not(z3.Implies(pre_z3, wp_result)))
    if s.check() == sat:
        print(f"  Main VC (pre → wp): INVALID")
        all_ok = False
    else:
        print(f"  Main VC (pre → wp): Valid")

    for vc_name, vc in side_vcs:
        s = Solver()
        s.add(z3.Not(vc))
        if s.check() == sat:
            print(f"  Side VC ({vc_name}): INVALID")
            all_ok = False
        else:
            print(f"  Side VC ({vc_name}): Valid")

    if all_ok:
        print(f"  Result: Verified")
    else:
        print(f"  Result: FAILED")
    print()


# ============================================================================
# Test Programs for Part (b) — verify your VCG works on these
# ============================================================================

def test_swap():
    """{ x == a ∧ y == b }  t:=x; x:=y; y:=t  { x == b ∧ y == a }"""
    pre = ImpAnd(Compare('==', Var('x'), Var('a')),
                 Compare('==', Var('y'), Var('b')))
    stmt = Seq(Assign('t', Var('x')),
               Seq(Assign('x', Var('y')), Assign('y', Var('t'))))
    post = ImpAnd(Compare('==', Var('x'), Var('b')),
                  Compare('==', Var('y'), Var('a')))
    verify(pre, stmt, post, "Swap")


def test_abs():
    """{ true }  if x<0 then r:=0-x else r:=x  { r >= 0 ∧ (r==x ∨ r==0-x) }"""
    pre = BoolConst(True)
    stmt = If(Compare('<', Var('x'), IntConst(0)),
              Assign('r', BinOp('-', IntConst(0), Var('x'))),
              Assign('r', Var('x')))
    post = ImpAnd(Compare('>=', Var('r'), IntConst(0)),
                  ImpOr(Compare('==', Var('r'), Var('x')),
                        Compare('==', Var('r'), BinOp('-', IntConst(0), Var('x')))))
    verify(pre, stmt, post, "Absolute Value")


# ============================================================================
# Part (c): Invariant Discovery — 8 pts
#
# For each program below, replace the `???` invariant with a correct one.
# [EXPLAIN] in a comment how you found each invariant and why it works.
# ============================================================================

def test_mult():
    """
    Program C1 — Multiplication by addition:
      { a >= 0 }
      i := 0; r := 0;
      while i < a  invariant ???  do
        r := r + b;  i := i + 1;
      { r == a * b }

    TODO: Replace the invariant below with a correct one.
    """
    pre = Compare('>=', Var('a'), IntConst(0))
    # [EXPLAIN] Invariant: r == i * b ∧ i <= a.
    # The loop adds b to r each iteration while incrementing i, so r always equals i*b.
    # We also need i <= a to bound the loop counter. When the loop exits (i >= a),
    # combined with i <= a from the invariant, we get i == a, so r == a * b.
    inv = ImpAnd(Compare('==', Var('r'), BinOp('*', Var('i'), Var('b'))),
                 Compare('<=', Var('i'), Var('a')))
    body = Seq(Assign('r', BinOp('+', Var('r'), Var('b'))),
               Assign('i', BinOp('+', Var('i'), IntConst(1))))
    stmt = Seq(Assign('i', IntConst(0)),
               Seq(Assign('r', IntConst(0)),
                   While(Compare('<', Var('i'), Var('a')), inv, body)))
    post = Compare('==', Var('r'), BinOp('*', Var('a'), Var('b')))
    verify(pre, stmt, post, "C1: Multiplication by Addition")


def test_add():
    """
    Program C2 — Addition by loop:
      { n >= 0 ∧ m >= 0 }
      i := 0; r := n;
      while i < m  invariant ???  do
        r := r + 1;  i := i + 1;
      { r == n + m }

    TODO: Replace the invariant below with a correct one.
    """
    pre = ImpAnd(Compare('>=', Var('n'), IntConst(0)),
                 Compare('>=', Var('m'), IntConst(0)))
    # [EXPLAIN] Invariant: r == n + i ∧ i <= m.
    # r starts at n and i at 0; each iteration increments both by 1, maintaining r == n + i.
    # The bound i <= m ensures that when the loop exits (i >= m), we get i == m, so r == n + m.
    inv = ImpAnd(Compare('==', Var('r'), BinOp('+', Var('n'), Var('i'))),
                 Compare('<=', Var('i'), Var('m')))
    body = Seq(Assign('r', BinOp('+', Var('r'), IntConst(1))),
               Assign('i', BinOp('+', Var('i'), IntConst(1))))
    stmt = Seq(Assign('i', IntConst(0)),
               Seq(Assign('r', Var('n')),
                   While(Compare('<', Var('i'), Var('m')), inv, body)))
    post = Compare('==', Var('r'), BinOp('+', Var('n'), Var('m')))
    verify(pre, stmt, post, "C2: Addition by Loop")


def test_sum():
    """
    Program C3 — Sum of 1..n:
      { n >= 1 }
      i := 1; s := 0;
      while i <= n  invariant ???  do
        s := s + i;  i := i + 1;
      { 2 * s == n * (n + 1) }

    TODO: Replace the invariant below with a correct one.
    """
    pre = Compare('>=', Var('n'), IntConst(1))
    # [EXPLAIN] Invariant: 2*s == (i-1)*i ∧ i >= 1 ∧ i <= n+1.
    # s accumulates the sum 1+2+...+(i-1), so 2*s = (i-1)*i by the closed-form formula.
    # When the loop exits (i > n), combined with i <= n+1, we get i == n+1,
    # so 2*s = n*(n+1) which matches the postcondition.
    inv = ImpAnd(
        Compare('==', BinOp('*', IntConst(2), Var('s')),
                BinOp('*', BinOp('-', Var('i'), IntConst(1)), Var('i'))),
        ImpAnd(Compare('>=', Var('i'), IntConst(1)),
               Compare('<=', Var('i'), BinOp('+', Var('n'), IntConst(1)))))
    body = Seq(Assign('s', BinOp('+', Var('s'), Var('i'))),
               Assign('i', BinOp('+', Var('i'), IntConst(1))))
    stmt = Seq(Assign('i', IntConst(1)),
               Seq(Assign('s', IntConst(0)),
                   While(Compare('<=', Var('i'), Var('n')), inv, body)))
    post = Compare('==', BinOp('*', IntConst(2), Var('s')),
                   BinOp('*', Var('n'), BinOp('+', Var('n'), IntConst(1))))
    verify(pre, stmt, post, "C3: Sum of 1..n")


# ============================================================================
# Part (d): Find the Bug — 4 pts
#
# The invariant below is WRONG (too weak). Your VCG should report failure.
# 1. Run it — which side VC fails?
# 2. [EXPLAIN] Give a concrete state where the invariant holds but the
#    postcondition does not.
# 3. Fix the invariant and re-verify.
# ============================================================================

def test_buggy_div():
    """
    Integer division with a BUGGY invariant.
      { x >= 0 ∧ y > 0 }
      q := 0; r := x;
      while r >= y  invariant (q * y + r == x)  do    ← TOO WEAK!
        r := r - y;  q := q + 1;
      { q * y + r == x ∧ 0 <= r ∧ r < y }

    The invariant q * y + r == x is correct but INCOMPLETE.
    It is missing a crucial conjunct. Find it.
    """
    pre = ImpAnd(Compare('>=', Var('x'), IntConst(0)),
                 Compare('>', Var('y'), IntConst(0)))

    # BUGGY invariant — intentionally too weak
    inv_buggy = Compare('==',
        BinOp('+', BinOp('*', Var('q'), Var('y')), Var('r')),
        Var('x'))

    body = Seq(Assign('r', BinOp('-', Var('r'), Var('y'))),
               Assign('q', BinOp('+', Var('q'), IntConst(1))))
    stmt = Seq(Assign('q', IntConst(0)),
               Seq(Assign('r', Var('x')),
                   While(Compare('>=', Var('r'), Var('y')),
                         inv_buggy, body)))
    post = ImpAnd(Compare('==',
                       BinOp('+', BinOp('*', Var('q'), Var('y')), Var('r')),
                       Var('x')),
                  ImpAnd(Compare('>=', Var('r'), IntConst(0)),
                         Compare('<', Var('r'), Var('y'))))

    verify(pre, stmt, post, "Buggy Division (should FAIL)")

    # [EXPLAIN] The postcondition side VC fails. The buggy invariant q*y + r == x does not
    # track that r >= 0, so a counterexample is: x=0, y=1, q=1, r=-1 where q*y+r == 0 == x
    # holds and the loop exits (r < y), but r < 0 violates the postcondition 0 <= r.
    # Fix: add r >= 0 to the invariant.
    inv_fixed = ImpAnd(
        Compare('==', BinOp('+', BinOp('*', Var('q'), Var('y')), Var('r')), Var('x')),
        Compare('>=', Var('r'), IntConst(0)))
    stmt_fixed = Seq(Assign('q', IntConst(0)),
                     Seq(Assign('r', Var('x')),
                         While(Compare('>=', Var('r'), Var('y')),
                               inv_fixed, body)))
    verify(pre, stmt_fixed, post, "FIXED: Division")


# ============================================================================
# Part (a): WP Derivation via Z3 — 6 pts
#
# Build the following program as an IMP AST:
#   x := x + 1;
#   if x > 0 then y := x * 2 else y := 0 - x;
# Postcondition: { y > 0 }
#
# 1. Call wp() to get the weakest precondition. Print the Z3 formula.
# 2. Use Z3 to check whether each of the following is a valid precondition:
#    - { x >= 0 }
#    - { x >= -1 }
#    - { x == -1 }
#    For each, print whether it's valid and add a comment explaining why.
# ============================================================================

def test_wp_derivation():
    """
    Part (a): Use your VCG to compute wp, then check candidate preconditions.
    TODO: Implement after you finish Part (b).
    """
    print("=== Part (a): WP Derivation ===")

    # x := x + 1; if x > 0 then y := x * 2 else y := 0 - x
    stmt = Seq(
        Assign('x', BinOp('+', Var('x'), IntConst(1))),
        If(Compare('>', Var('x'), IntConst(0)),
           Assign('y', BinOp('*', Var('x'), IntConst(2))),
           Assign('y', BinOp('-', IntConst(0), Var('x')))))
    post = Compare('>', Var('y'), IntConst(0))

    wp_result = wp(stmt, bexp_to_z3(post))
    print(f"  wp = {simplify(wp_result)}")

    candidates = [
        ("x >= 0",  z3_var('x') >= 0),
        ("x >= -1", z3_var('x') >= -1),
        ("x == -1", z3_var('x') == -1),
    ]
    for name, pre in candidates:
        s = Solver()
        s.add(z3.Not(z3.Implies(pre, wp_result)))
        valid = (s.check() == unsat)
        print(f"  {name}: {'VALID' if valid else 'INVALID'}")

    # [EXPLAIN] x >= 0: VALID. After x := x+1, x >= 1 > 0 so we take the then-branch,
    #   y = x*2 >= 2 > 0. The precondition is strong enough to guarantee y > 0.
    # [EXPLAIN] x >= -1: INVALID. When x = -1, after x := x+1, x = 0 which is not > 0,
    #   so we take the else-branch: y = 0 - 0 = 0, which does not satisfy y > 0.
    # [EXPLAIN] x == -1: INVALID. Same counterexample as above: x = -1 leads to y = 0.

    print()


# ============================================================================
if __name__ == "__main__":
    print("=" * 60)
    print("Part (b): VCG Correctness Tests")
    print("=" * 60)
    test_swap()
    test_abs()

    print("=" * 60)
    print("Part (a): WP Derivation via Z3")
    print("=" * 60)
    test_wp_derivation()

    print("=" * 60)
    print("Part (c): Invariant Discovery")
    print("=" * 60)
    test_mult()
    test_add()
    test_sum()

    print("=" * 60)
    print("Part (d): Find the Bug")
    print("=" * 60)
    test_buggy_div()
