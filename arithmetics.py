import sys

from main import Term, normalize, VarSet

from typing import Tuple

import time


def num(n: int) -> Term:
    s = Term.new_var("z0")
    o = Term.new_var("z1")
    result = o
    for i in range(n):
        result = s(result)

    return result.abstract(s, o)


T = Term.parse("λz0.λz1.z0")
F = Term.parse("λz0.λz1.z1")

increment = Term.parse(f"λz2.(λz0.λz1.z2z0(z0z1))")


def tuple(*args: Term) -> Term:
    var_set = VarSet()
    for arg in args:
        var_set.update(arg.free_vars())
    z_fresh = var_set.pick_fresh()
    result = Term.new_var(z_fresh)
    for arg in args:
        result = result(arg)
    return result.abstract(z_fresh)


def kth_accessor(k: int, n: int):
    s = ""
    for i in range(n):
        s += f"λz{i}."
    s += f"z{k}"
    return Term.parse(s)


def expect_eq(lhs: Term, rhs: Term):
    if lhs != rhs:
        raise Exception(f"{lhs} != {rhs}")


def expect_reduction(lhs: Term, rhs: Term, **kwargs):
    lhs_norm = normalize(lhs, **kwargs)
    if lhs_norm != rhs:
        raise Exception(f"{lhs} -> {lhs_norm} != {rhs}")


def build_decrement_transition():
    # z0: pair (a, b)
    # transition: (a, b) -> (b, b + 1)
    z0 = Term.new_var("z0")
    get_second = kth_accessor(1, 2)
    new_first = z0(get_second)
    new_second = increment(z0(get_second))
    new_pair = tuple(new_first, new_second)
    transition = new_pair.abstract(z0)

    return transition


decrement_transition = build_decrement_transition()


def build_decrement():
    # z0: num(n)
    z0 = Term.new_var("z0")
    initial_pair = tuple(num(0), num(0))
    get_first = kth_accessor(0, 2)
    return (z0(decrement_transition, initial_pair))(get_first).abstract(z0)


decrement = build_decrement()


def build_zero():
    always_false = F.abstract("z0")
    n = Term.new_var("z0")
    return n(always_false, T).abstract(n)


zero = build_zero()


def build_add():
    a = Term.new_var("z0")
    b = Term.new_var("z1")
    s = Term.new_var("z2")
    o = Term.new_var("z3")
    return a(s, b(s, o)).abstract(a, b, s, o)


add = build_add()


def build_mul():
    a = Term.new_var("z0")
    b = Term.new_var("z1")
    s = Term.new_var("z2")
    return a(b(s)).abstract(a, b, s)


mul = build_mul()


def measure_mul_complexity():
    n = 1
    while n <= 16384:
        start_time = time.time()
        expect_reduction(mul(num(0), num(n)), num(0))
        finish_time = time.time()
        print(f"{0} x {n} took {finish_time - start_time} seconds :)")
        n *= 2


def build_Y():
    action = Term.new_var("z0")
    var = Term.new_var("z1")
    block = action(var(var)).abstract(var)
    return block(block).abstract(action)


Y = build_Y()


def build_power_of_two():
    phi = Term.new_var("z0")
    n = Term.new_var("z1")
    formula = zero(n)(num(1), mul(phi(decrement(n)), num(2)))
    action = formula.abstract(phi, n)
    return Y(action)


power_of_two = build_power_of_two()


if __name__ == "__main__":
    sys.setrecursionlimit(10**9)

    n5 = num(5)
    print(n5)
    n5_inc = increment(n5)
    print(n5_inc)
    n6 = num(6)
    expect_reduction(n5_inc, n6)

    t = tuple(num(3), num(6), num(9))
    a = kth_accessor(1, 3)
    ta = Term.parse(f"({t})({a})")

    print(t)
    print(a)
    print(ta)

    expect_reduction(ta, num(6))

    pair = tuple(num(2), num(3))
    print(pair)
    print(decrement_transition)
    next_pair = decrement_transition(pair)
    print(next_pair)
    expected_pair = tuple(num(3), num(4))
    expect_eq(normalize(next_pair, verbose=True, separate_lines=True), expected_pair)

    expect_reduction(decrement(num(4)), num(3))

    expect_reduction(zero(num(0)), T, verbose=True, separate_lines=True)
    expect_reduction(zero(num(1)), F)

    expect_reduction(add(num(3), num(5)), num(8))

    # measure_mul_complexity()

    #expect_reduction(mul(num(1000), num(0)), num(0))

    expect_reduction(power_of_two(num(5)), num(32), print_step_count=True)
