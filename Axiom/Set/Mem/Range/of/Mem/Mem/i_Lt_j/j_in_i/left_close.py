from util import *


@apply
def apply(contains_j, contains_i):
    j, Sj = contains_j.of(Element)
    i, Si = contains_i.of(Element)

    if not Sj._has(i):
        i, Si, j, Sj = j, Sj, i, Si
    assert Sj._has(i)

    a_d, n_d = Si.of(Range)
    i_d, n = Sj.of(Range)

    d = i - i_d

    a = a_d - d
    assert n_d == n + d + 1

    return Element(i, Range(a + d, d + j + 1)), Element(j, Range(a - 1, n))


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    a, i, j, n, d = Symbol(integer=True)
    Eq << apply(Element(j, Range(i - d + 1, n)), Element(i, Range(a + d, d + n)))

    Eq << Set.MemSub.of.Mem_Icc.apply(Eq[1], d)

    Eq << Set.Mem.given.Mem.Sub.apply(Eq[2], d)

    Eq <<= Set.Mem_Range.given.And.apply(Eq[-1]), Set.Mem_Range.given.And.apply(Eq[3])

    Eq <<= Set.And.of.Mem_Range.apply(Eq[0]), Set.And.of.Mem_Range.apply(Eq[4])

    Eq << Algebra.Gt.of.Ge.relax.apply(Eq[-2])

    Eq << Algebra.Gt.of.Gt.Ge.apply(Eq[-1], Eq[6])

    Eq << Algebra.Ge.of.Gt.relax.apply(Eq[-1])

    Eq << Eq[-2].reversed


if __name__ == '__main__':
    run()

# created on 2020-03-06
