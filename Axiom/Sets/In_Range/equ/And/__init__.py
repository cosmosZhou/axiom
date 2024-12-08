from util import *


@apply
def apply(given):
    x, domain = given.of(Element)
    a, b = domain.of(Range)
    assert x.is_integer
    return And(x >= a, x < b)

@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x, a, b = Symbol(integer=True)
    Eq << apply(Element(x, Range(a, b)))

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Sets.In_Range.to.And, simplify=False)

    Eq << Eq[-1].this.rhs.apply(Sets.Lt.Ge.to.In.Range)


if __name__ == '__main__':
    run()
# created on 2020-03-24

from . import split
