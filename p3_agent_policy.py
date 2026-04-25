"""
CS292C Homework 2 — Problem 3: Agent Permission Policy Verification (25 points)
=================================================================================
Encode a realistic agent permission policy as SMT formulas and use Z3 to
analyze it for safety properties and privilege escalation vulnerabilities.
"""

from z3 import *

# ============================================================================
# Constants
# ============================================================================

FILE_READ = 0
FILE_WRITE = 1
SHELL_EXEC = 2
NETWORK_FETCH = 3

ADMIN = 0
DEVELOPER = 1
VIEWER = 2

# ============================================================================
# Sorts and Functions
#
# You will use these to build your policy encoding.
# Do NOT modify these declarations.
# ============================================================================

User = DeclareSort('User')
Resource = DeclareSort('Resource')

role         = Function('role', User, IntSort())          # 0=admin, 1=dev, 2=viewer
is_sensitive = Function('is_sensitive', Resource, BoolSort())
in_sandbox   = Function('in_sandbox', Resource, BoolSort())
owner        = Function('owner', Resource, User)

# The core predicate: is this (user, tool, resource) triple allowed?
allowed = Function('allowed', User, IntSort(), Resource, BoolSort())


# ============================================================================
# Part (a): Encode the Policy — 10 pts
#
# Encode rules R1–R5 from the README as Z3 constraints.
#
# You must design the encoding yourself. Consider:
# - Use ForAll to make rules apply to all users/resources.
# - Encode both what IS allowed and what is NOT allowed.
# - Rule R4 overrides R3 — handle this carefully.
#
# Return a list of Z3 constraints.
# ============================================================================

def make_policy(include_r4=True):
    """
    Return a list of Z3 constraints encoding rules R1–R5.
    Uses a closed-world biconditional: allowed iff explicitly permitted and not overridden.
    """
    u = Const('u', User)
    r = Const('r', Resource)
    t = Int('t')

    constraints = []

    # Valid roles
    constraints.append(ForAll([u], Or(role(u) == ADMIN, role(u) == DEVELOPER, role(u) == VIEWER)))

    # Positive authorization: who is granted access
    positive = Or(
        role(u) == ADMIN,                                                              # R3
        And(role(u) == DEVELOPER, t == FILE_READ),                                     # R2
        And(role(u) == DEVELOPER, t == FILE_WRITE, Or(owner(r) == u, in_sandbox(r))),  # R2
        And(role(u) == VIEWER, t == FILE_READ, Not(is_sensitive(r))),                   # R1
    )

    # Negative overrides: restrictions that apply to everyone
    overrides = [Not(And(t == NETWORK_FETCH, Not(in_sandbox(r))))]  # R5
    if include_r4:
        overrides.append(Not(And(t == SHELL_EXEC, is_sensitive(r))))  # R4

    # Closed-world: allowed iff positive grant and no override blocks it
    constraints.append(ForAll([u, t, r],
        allowed(u, t, r) == And(positive, *overrides)))

    return constraints


# ============================================================================
# Part (b): Policy Queries — 8 pts
# ============================================================================

def query(description, policy, extra):
    """Helper: check if extra constraints are SAT under the policy."""
    s = Solver()
    s.add(policy)
    s.add(extra)
    result = s.check()
    print(f"  {description}")
    print(f"  → {result}")
    if result == sat:
        m = s.model()
        print(f"    Model: {m}")
    print()
    return result


def part_b():
    """
    Answer the four queries from the README.
    For query 4, also demonstrate what becomes possible without R4.
    """
    policy = make_policy()
    print("=== Part (b): Policy Queries ===\n")

    u = Const('u', User)
    r = Const('r', Resource)

    # Q1: Can a developer write to a sensitive file they don't own, in the sandbox?
    query("Q1: developer file_write sensitive, not-owned, sandbox?", policy, [
        role(u) == DEVELOPER,
        allowed(u, FILE_WRITE, r),
        is_sensitive(r),
        owner(r) != u,
        in_sandbox(r),
    ])
    # [EXPLAIN] SAT — R2 allows developers to file_write any sandbox resource. R4 only
    # restricts shell_exec, not file_write, so sensitivity does not block this.

    # Q2: Can an admin network_fetch a resource outside the sandbox?
    query("Q2: admin network_fetch outside sandbox?", policy, [
        role(u) == ADMIN,
        allowed(u, NETWORK_FETCH, r),
        Not(in_sandbox(r)),
    ])
    # [EXPLAIN] UNSAT — R5 restricts network_fetch to sandbox resources only,
    # and this override applies to all roles including admins.

    # Q3: Is there ANY role that can shell_exec on a sensitive resource?
    query("Q3: any role shell_exec on sensitive?", policy, [
        allowed(u, SHELL_EXEC, r),
        is_sensitive(r),
    ])
    # [EXPLAIN] UNSAT — R4 blocks shell_exec on sensitive resources for ALL roles,
    # overriding even the admin's blanket R3 permission.

    # Q4: Remove R4, what dangerous action becomes possible?
    policy_no_r4 = make_policy(include_r4=False)
    query("Q4: without R4, admin shell_exec on sensitive?", policy_no_r4, [
        role(u) == ADMIN,
        allowed(u, SHELL_EXEC, r),
        is_sensitive(r),
    ])
    # [EXPLAIN] SAT — Without R4, R3 grants admins unrestricted tool access. Admins can now
    # shell_exec on sensitive resources, which could lead to data exfiltration or system
    # compromise. R4 was the only safeguard preventing this.


# ============================================================================
# Part (c): Privilege Escalation — 7 pts
#
# New rule R6: Developers may shell_exec on non-sensitive sandbox resources.
#
# Attack scenario: A developer uses shell_exec on a non-sensitive sandbox
# resource to change ANOTHER resource's sensitivity flag (e.g., modifying
# a config file that controls access). This makes a previously sensitive
# resource become non-sensitive, bypassing R4 on the next step.
#
# Model this as a 2-step trace where a resource's sensitivity changes
# between steps.
# ============================================================================

def part_c():
    """
    Model a 2-step privilege escalation where a developer uses shell_exec
    to change a resource's sensitivity flag, then exploits the change.
    """
    print("=== Part (c): Privilege Escalation ===\n")

    is_sens_1 = Function('is_sensitive_step1', Resource, BoolSort())
    is_sens_2 = Function('is_sensitive_step2', Resource, BoolSort())
    allowed_1 = Function('allowed_step1', User, IntSort(), Resource, BoolSort())
    allowed_2 = Function('allowed_step2', User, IntSort(), Resource, BoolSort())

    def make_step_policy(is_sens_fn, allowed_fn):
        """Build policy with R1-R5 + R6 using given sensitivity/allowed functions."""
        u = Const('u_p', User)
        r = Const('r_p', Resource)
        t = Int('t_p')

        positive = Or(
            role(u) == ADMIN,
            And(role(u) == DEVELOPER, t == FILE_READ),
            And(role(u) == DEVELOPER, t == FILE_WRITE, Or(owner(r) == u, in_sandbox(r))),
            And(role(u) == VIEWER, t == FILE_READ, Not(is_sens_fn(r))),
            # R6: developers may shell_exec on non-sensitive sandbox resources
            And(role(u) == DEVELOPER, t == SHELL_EXEC, Not(is_sens_fn(r)), in_sandbox(r)),
        )
        override = And(
            Not(And(t == SHELL_EXEC, is_sens_fn(r))),
            Not(And(t == NETWORK_FETCH, Not(in_sandbox(r)))),
        )
        return ForAll([u, t, r], allowed_fn(u, t, r) == And(positive, override))

    dev = Const('dev', User)
    r1 = Const('r1', Resource)
    r2 = Const('r2', Resource)
    u_all = Const('u_all', User)

    # --- Demonstrate the escalation ---
    s = Solver()
    s.add(ForAll([u_all], Or(role(u_all) == ADMIN, role(u_all) == DEVELOPER, role(u_all) == VIEWER)))
    s.add(make_step_policy(is_sens_1, allowed_1))
    s.add(make_step_policy(is_sens_2, allowed_2))

    s.add(role(dev) == DEVELOPER)
    s.add(r1 != r2)

    # Initial state: r1 non-sensitive sandbox, r2 sensitive sandbox
    s.add(Not(is_sens_1(r1)))
    s.add(in_sandbox(r1))
    s.add(is_sens_1(r2))
    s.add(in_sandbox(r2))

    # Step 1: dev shell_exec on r1 — allowed by R6
    s.add(allowed_1(dev, SHELL_EXEC, r1))

    # Side effect: shell_exec on r1 flips r2's sensitivity to False
    s.add(Not(is_sens_2(r2)))
    s.add(is_sens_2(r1) == is_sens_1(r1))

    # Step 2: dev shell_exec on r2 — now non-sensitive, so R6 allows it
    s.add(allowed_2(dev, SHELL_EXEC, r2))

    result = s.check()
    print(f"  Can developer bypass R4 via 2-step escalation? {result}")
    if result == sat:
        print(f"    Step 1: dev shell_exec on r1 (non-sensitive, sandbox) — allowed by R6")
        print(f"    Side-effect: r2 sensitivity changed from True to False")
        print(f"    Step 2: dev shell_exec on r2 (now non-sensitive, sandbox) — allowed by R6")
        print(f"    Developer effectively bypassed R4 on originally-sensitive r2!")
    print()

    # [EXPLAIN] Fix: Enforce immutable sensitivity labels. The vulnerability arises because
    # R4 and R6 check current sensitivity, which shell_exec can modify at runtime. The fix
    # adds an integrity constraint that sensitivity labels cannot change between steps.
    # With this, r2 remains sensitive in step 2 and R4 blocks the shell_exec.
    print("  --- Fix: immutable sensitivity labels ---")

    s_fix = Solver()
    s_fix.add(ForAll([u_all], Or(role(u_all) == ADMIN, role(u_all) == DEVELOPER, role(u_all) == VIEWER)))
    s_fix.add(make_step_policy(is_sens_1, allowed_1))
    s_fix.add(make_step_policy(is_sens_2, allowed_2))
    s_fix.add(role(dev) == DEVELOPER)
    s_fix.add(r1 != r2)
    s_fix.add(Not(is_sens_1(r1)))
    s_fix.add(in_sandbox(r1))
    s_fix.add(is_sens_1(r2))
    s_fix.add(in_sandbox(r2))
    s_fix.add(allowed_1(dev, SHELL_EXEC, r1))

    # Fix: sensitivity labels are immutable across steps
    r_fix = Const('r_fix', Resource)
    s_fix.add(ForAll([r_fix], is_sens_2(r_fix) == is_sens_1(r_fix)))

    # Attempt the escalation
    s_fix.add(allowed_2(dev, SHELL_EXEC, r2))

    result = s_fix.check()
    if result == unsat:
        print("  ESCALATION BLOCKED")
    else:
        print(f"  Fix failed: {result}")
    print()


# ============================================================================
if __name__ == "__main__":
    part_b()
    part_c()
