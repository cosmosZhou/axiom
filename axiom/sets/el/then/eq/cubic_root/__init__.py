from util import *


@apply
def apply(contains_p):
    arg_p, domain = contains_p.of(Element)
    p = arg_p.of(Arg)
    assert domain in Interval(-S.Pi / 3, S.Pi / 3, left_open=True)
    return Equal((p ** 3) ** (S.One / 3), p)


@prove
def prove(Eq):
    from axiom import sets, algebra

    p = Symbol(complex=True, given=True)
    Eq << apply(Element(Arg(p), Interval(-S.Pi / 3, S.Pi / 3, left_open=True)))

    Eq << sets.el.then.el.mul.interval.apply(Eq[0], 3)

    Eq << sets.el.then.el.sub.apply(Eq[-1], S.Pi)

    Eq << sets.el.then.el.div.interval.apply(Eq[-1], S.Pi * 2)

    Eq << sets.el.then.ceiling_is_zero.apply(Eq[-1])
    Eq << Eq[-1].this.find(Mul).apply(algebra.mul.to.add)

    Eq << Eq[1].this.lhs.apply(algebra.root.to.mul.expi.arg)

    Eq << Eq[-1].this.find(Arg).apply(algebra.arg.pow.to.add)

    Eq << Eq[-1].subs(Eq[-3])

    Eq << Eq[-1].this.rhs.apply(algebra.expr.to.mul.expi)


if __name__ == '__main__':
    run()
from . import second
from . import third
# created on 2021-03-08
