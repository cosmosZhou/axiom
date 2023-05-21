from util import *


@apply
def apply(lt, gt):
    x, y = lt.of(Less)
    S[x], S[-y] = gt.of(Greater)
    return Less(abs(x), y)


@prove
def prove(Eq):
    from axiom import algebra

    y, x = Symbol(real=True)
    Eq << apply(x < y, x > -y)

    Eq << Eq[-1].this.lhs.apply(algebra.abs.to.piece)

    Eq << Eq[-1].apply(algebra.cond_piece.given.ou)

    Eq << algebra.cond.given.et.restrict.apply(Eq[-1], cond=Eq[0])

    Eq << algebra.et.given.et.subs.bool.apply(Eq[-1], 0)

    Eq << -Eq[1]

    Eq << algebra.cond.given.et.restrict.apply(Eq[-2], cond=Eq[-1])

    Eq << algebra.et.given.et.subs.bool.apply(Eq[-1], index=0)

    
    


if __name__ == '__main__':
    run()

from . import both
from . import max
# created on 2018-07-29
# updated on 2023-05-20
