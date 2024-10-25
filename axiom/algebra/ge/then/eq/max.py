from util import *


@apply
def apply(given, reverse=False):
    a, b = given.of(GreaterEqual)
    if False:
        return Equal(a, Max(a, b))
    return Equal(Max(a, b), a)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x >= y)

    Eq << Eq[-1].this.lhs.apply(algebra.max.to.piece)

    Eq << algebra.cond.cond.of.et.subs.apply(Eq[0], Eq[-1])




if __name__ == '__main__':
    run()
# created on 2018-09-05
# updated on 2023-06-23
