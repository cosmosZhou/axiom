from util import *


@apply
def apply(given):
    x = given.of(Equal[frac, 0])
    return Element(x, Integers)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True, given=True)

    Eq << apply(Equal(frac(x), 0))

    Eq << Eq[0].this.lhs.apply(algebra.frac.to.add)

    Eq << Eq[1].subs(Eq[-1].reversed)



if __name__ == '__main__':
    run()

# created on 2018-05-10
