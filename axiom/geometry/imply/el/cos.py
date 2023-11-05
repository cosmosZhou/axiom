from util import *


@apply(simplify=False)
def apply(x):
    return Element(cos(x), Interval(-1, 1))


@prove
def prove(Eq):
    from axiom import geometry, algebra, sets

    x = Symbol(real=True)
    Eq << apply(x)

    Eq << geometry.imply.eq.add.square.apply(x)

    Eq << algebra.eq_add.imply.le.bounded.apply(Eq[1], 1)

    Eq << Eq[-1].this.apply(sets.square_le.to.el.interval)

    


if __name__ == '__main__':
    run()
# created on 2023-10-03
