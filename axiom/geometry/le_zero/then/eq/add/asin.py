from util import *


@apply
def apply(is_nonpositive):
    x = is_nonpositive.of(Expr <= 0)
    assert x in Interval(-1, 1)
    return Equal(asin(sqrt(1 - x ** 2)) - asin(x), S.Pi / 2)


@prove
def prove(Eq):
    from axiom import geometry, algebra, sets

    x = Symbol(domain=Interval(-1, 1))
    Eq << apply(x <= 0)

    Eq << geometry.cos.to.sub.apply(cos(Eq[1].lhs))

    Eq << algebra.le_zero.then.eq.abs.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(geometry.cos.neg)
    Eq << geometry.cos_is_zero.then.any.eq.apply(Eq[-1])

    Eq << -Eq[-1].this.expr

    Eq << Eq[-1].this.apply(algebra.any.limits.negate.oo)

    Eq << algebra.any.then.any.limits.subs.offset.apply(Eq[-1], 1)

    Eq.any_eq = Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << GreaterEqual(x, -1, plausible=True)

    Eq << sets.ge.le.then.el.interval.apply(Eq[-1], Eq[0])

    Eq <<= geometry.el.then.el.asin.apply(Eq[-1]), sets.el.then.el.sqrt.max.apply(Eq[-1])

    Eq <<= sets.el.then.el.neg.apply(Eq[-2]), geometry.el.then.el.asin.apply(Eq[-1])

    Eq << sets.el.el.then.el.add.interval.apply(Eq[-1], Eq[-2])

    Eq << algebra.cond.any.then.any.et.apply(Eq[-1], Eq.any_eq, simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.then.cond.subs, ret=0)

    Eq << Eq[-1].this.find(Element).apply(sets.el.then.el.sub, S.Pi / 2)

    Eq << Eq[-1].this.find(Element).apply(sets.el.then.el.div.interval, S.Pi)

    # https://en.wikipedia.org/wiki/Argument_(complex_analysis)



if __name__ == '__main__':
    run()
# created on 2018-07-13
# updated on 2023-05-20
