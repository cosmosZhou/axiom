from util import *


@apply
def apply(fraction):
    x = fraction.of(FractionalPart)

    return Equal(fraction, x + ceil(-x))


@prove
def prove(Eq):
    from Axiom import Algebra
    x = Symbol(real=True)
    Eq << apply(frac(x))

    Eq << Eq[-1].this.lhs.apply(Algebra.Fract.eq.Sub_Floor)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ceil.eq.Add.Fract)

    Eq << Eq[-1].this.find(FractionalPart).apply(Algebra.Fract.eq.Sub_Floor)

if __name__ == '__main__':
    run()
# created on 2019-05-14
