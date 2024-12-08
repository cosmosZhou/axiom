from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    a, b = domain.of(Interval)
    assert a >= 0
    return Element(sqrt(x), domain.copy(start=sqrt(a), stop=sqrt(b)))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(real=True)
    a, b = Symbol(real=True, nonnegative=True)
    Eq << apply(Element(x, Interval(a, b, right_open=True)))

    Eq << Sets.In_Interval.of.And.apply(Eq[1])

    Eq << Sets.In_Interval.to.And.apply(Eq[0])

    Eq << Algebra.Ge.to.Ge.Sqrt.apply(Eq[-2])

    Eq << Algebra.Ge.to.Ge.relax.apply(Eq[-2], lower=0)

    Eq << Algebra.Ge_0.Lt.to.Lt.Sqrt.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()

# created on 2019-06-28

del Max
from . import Max
