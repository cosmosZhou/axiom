from util import *


@apply
def apply(given):
    x = given.of(Unequal[0])
    assert x.is_real
    return Element(x, Reals - {0})


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol(real=True)
    Eq << apply(Unequal(x, 0))

    Eq << algebra.ne_zero.then.ou.apply(Eq[0])

    Eq << Eq[-1].this.args[1].apply(sets.gt_zero.then.is_positive, simplify=None)

    Eq << Eq[-1].this.args[0].apply(sets.lt_zero.then.is_negative, simplify=None)

    Eq << sets.ou.then.el.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-05-02
