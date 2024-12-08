from util import *


@apply
def apply(contains_i, contains_j):
    i, Si = contains_i.of(Element)
    j, Sj = contains_j.of(Element)

    if not Si._has(j):
        i, Si, j, Sj = j, Sj, i, Si
    assert Si._has(j)

    _a, _b = Si.of(Range)
    _a -= j
    _b -= j

    assert not _a._has(j) and not _b._has(j)
    a, b = Sj.of(Range)

    return Element(i, Range(_a + a, _b + b - 1)), Element(j, Range(Max(a, i - _b + 1), Min(b, i - _a + 1)))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, i, j, n, m, d = Symbol(integer=True)
    Eq << apply(Element(i, Range(d + j, n + j)), Element(j, Range(a, m)))

    Eq.ge, Eq.lt = Sets.In_Range.to.And.apply(Eq[0])

    Eq << Eq.ge.this.apply(Algebra.Ge.transport, rhs=0)

    Eq << Eq.lt.this.apply(Algebra.Lt.transport, rhs=-1)

    Eq << Sets.Lt.Ge.to.In.Range.apply(Eq[-1], Eq[-2])

    Eq <<= Eq[1] & Eq[-1]

    Eq << Sets.In_Range.to.And.apply(Eq[1])

    Eq <<= Algebra.Ge.Ge.to.Ge.trans.apply(Eq.ge, Eq[-2] + d), Algebra.Lt.to.Le.strengthen.apply(Eq[-1])

    Eq << Algebra.Lt.Le.to.Lt.trans.apply(Eq.lt, Eq[-1] + n)

    Eq << Sets.Lt.Ge.to.In.Range.apply(Eq[-1], Eq[-3])


if __name__ == '__main__':
    run()
# created on 2020-03-20
