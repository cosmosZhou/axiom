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
    assert n_d == n + d

    return Element(i, Range(a + d, d + j + 1)), Element(j, Range(a, n))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, i, j, n, d = Symbol(integer=True)
    Eq << apply(Element(j, Range(i - d + 1, n)), Element(i, Range(a + d, d + n - 1)))

    Eq << Sets.In.to.In.Sub.apply(Eq[1], d)

    Eq << Sets.In.of.In.Sub.apply(Eq[2], d)

    Eq <<= Sets.In_Range.of.And.apply(Eq[-1]), Sets.In_Range.of.And.apply(Eq[3])

    Eq <<= Sets.In_Range.to.And.apply(Eq[0]), Sets.In_Range.to.And.apply(Eq[4])

    Eq << Algebra.Ge.to.Gt.relax.apply(Eq[-2])

    Eq << Algebra.Gt.Ge.to.Gt.trans.apply(Eq[-1], Eq[6])

    Eq << Eq[-2].reversed

    Eq << Algebra.Gt.to.Ge.strengthen.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-01-29
from . import left_close