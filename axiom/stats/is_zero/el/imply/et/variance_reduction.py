from util import *


@apply
def apply(eq, el):
    fx, *limits = eq.of(Equal[Expectation, Zero])
    b, interval = el.of(Element)
    
    ((gx, S[fx ** 2]), *S[limits]), (S[fx], *S[limits]) = interval.of(Interval[0, 2 * Expectation[Mul] / Expectation[Expr ** 2]])
    assert interval.left_open
    assert interval.right_open
    
    vars = {v for v, *_ in limits}
    from sympy.tensor.indexed import index_intersect
    random_symbols = index_intersect(gx.random_symbols, fx.random_symbols)
    assert random_symbols
    assert all (v in vars for v in random_symbols)
    return Equal(Expectation(fx * (gx - b)), Expectation(fx * gx)), Variance(fx * (gx - b)) < Variance(fx * gx)


@prove
def prove(Eq):
    from axiom import stats, algebra, sets

    x = Symbol(real=True, random=True)
    b = Symbol(real=True)
    π, Q = Function(real=True)
    Eq << apply(Equal(Expectation(π(x)), 0), Element(b, Interval(0, 2 * Expectation(π(x) ** 2 * Q(x)) / Expectation(π(x) ** 2), left_open=True, right_open=True)))

    Eq << Eq[-1].this.lhs.apply(stats.var.to.sub.expect)

    Eq << Eq[-1].this.find((~Pow) * Pow).apply(algebra.square.to.add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Expectation[Add]).apply(stats.expect.to.add)

    Eq << Eq[-1].this.find(Expectation[Add]).apply(stats.expect.to.add)

    Eq << Eq[-1].this.find(Expectation[-Symbol * Function]).apply(stats.expect.to.mul)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.find(Expectation).apply(stats.expect.to.mul)

    Eq << Eq[-1].this.find(Expectation[2]).apply(stats.expect.to.mul)

    Eq << Eq[-1].this.rhs.apply(stats.var.to.sub.expect)

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.mul)

    Eq << algebra.lt_zero.given.et.split.mul.apply(Eq[-1])

    Eq << algebra.lt_zero.given.lt.apply(Eq[-1])

    Eq << sets.el_interval.imply.et.apply(Eq[1])

    Eq << algebra.cond.imply.cond.domain_defined.apply(Eq[-1])

    Eq << algebra.ne_zero.imply.gt_zero.apply(Eq[-1])

    Eq << algebra.gt_zero.lt.imply.lt.mul.apply(Eq[-1], Eq[-3])

    Eq << Eq[2].this.find(Mul).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.lhs.apply(stats.expect.to.add)

    Eq << Eq[-1].this.lhs.apply(stats.expect.to.mul)

    Eq << Eq[-1].subs(Eq[0])
    


if __name__ == '__main__':
    run()
# created on 2023-04-14
# updated on 2024-03-11
