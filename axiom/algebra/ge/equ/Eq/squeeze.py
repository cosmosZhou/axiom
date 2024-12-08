from util import *


@apply
def apply(self):
    x, b = self.of(GreaterEqual)
    assert x <= b
    return Equal(x, b)


@prove
def prove(Eq):
    from Axiom import Algebra

    a = Symbol(integer=True)
    b = Symbol(integer=True, given=True)
    x = Symbol(domain=Range(a, b + 1), given=True)
    Eq << apply(x >= b)

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Ge.to.Eq.squeeze)

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.to.Ge)





if __name__ == '__main__':
    run()
# created on 2019-06-04
# updated on 2023-11-11

