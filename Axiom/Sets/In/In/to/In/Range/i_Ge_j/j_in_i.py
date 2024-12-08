from util import *


@apply
def apply(contains_j, contains_i):
    j, Sj = contains_j.of(Element)
    i, Si = contains_i.of(Element)

    if not Sj._has(i):
        i, Si, j, Sj = j, Sj, i, Si
    assert Sj._has(i)

    a_d, n = Si.of(Range)
    a, i_d = Sj.of(Range)

    d = i - i_d + 1
    assert a_d == a + d

    return Element(i, Range(d + j, n)), Element(j, Range(a, n - d))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, i, j, n, d = Symbol(integer=True)
    Eq << apply(Element(j, Range(a, i - d + 1)), Element(i, Range(a + d, n)))

    Eq <<= Sets.In_Range.of.And.apply(Eq[-2]), Sets.In_Range.of.And.apply(Eq[-1])

    Eq <<= Sets.In_Range.to.And.apply(Eq[0]), Sets.In_Range.to.And.apply(Eq[1])

    Eq << Eq[-2] + d

    Eq << Algebra.Lt.to.Le.strengthen.apply(Eq[-1])

    Eq << Algebra.Le.Lt.to.Lt.trans.apply(Eq[-1], Eq[5]) - d

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2019-11-05
