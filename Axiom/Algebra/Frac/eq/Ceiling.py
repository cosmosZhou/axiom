from util import *


@apply
def apply(fraction):
    x = fraction.of(FractionalPart)

    return Equal(fraction, x + ceiling(-x))


@prove
def prove(Eq):
    from Axiom import Algebra
    x = Symbol(real=True)
    Eq << apply(frac(x))

    Eq << Eq[-1].this.lhs.apply(Algebra.Frac.eq.Add)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ceiling.eq.Add.Frac)

    Eq << Eq[-1].this.find(FractionalPart).apply(Algebra.Frac.eq.Add)

if __name__ == '__main__':
    run()
# created on 2019-05-14
