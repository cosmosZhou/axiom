from util import *


@apply
def apply(ge_0, ge_1):
    x, a = ge_0.of(GreaterEqual)
    y, b = ge_1.of(GreaterEqual)
    return GreaterEqual(Min(x, y), Min(a, b))


@prove
def prove(Eq):
    from axiom import algebra

    a, x, y, b = Symbol(real=True, given=True)
    Eq << apply(x >= a, y >= b)

    Eq << Eq[-1].this.lhs.apply(algebra.min.to.piece)

    Eq << algebra.cond_piece.given.ou.apply(Eq[-1])

    Eq << ~Eq[-1]

    Eq << algebra.imply.ge_min.apply(a, b)

    Eq << algebra.ge.ge.imply.ge.transit.apply(Eq[0], Eq[-1])

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[-1], Eq[-3], invert=True)

    Eq << algebra.imply.ge_min.apply(b, a)

    Eq << algebra.ge.ge.imply.ge.transit.apply(Eq[1], Eq[-1])

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[-1], Eq[-3], invert=True)

    
    


if __name__ == '__main__':
    run()
# created on 2019-05-17
# updated on 2023-04-29
