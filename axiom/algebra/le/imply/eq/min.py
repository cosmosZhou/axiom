from util import *


@apply
def apply(given, reverse=False):
    a, b = given.of(LessEqual)
    if reverse:
        return Equal(a, Min(a, b))
    return Equal(Min(a, b), a)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x <= y)

    Eq << Eq[-1].this.lhs.apply(algebra.min.to.piece)

    Eq << algebra.cond.cond.given.et.subs.apply(Eq[0], Eq[-1])




if __name__ == '__main__':
    run()
# created on 2018-10-14
# updated on 2023-06-23
