from util import *


@apply
def apply(given):
    (fx, (x, S[1])), (S[x], domain) = given.of(All[Derivative >= 0])
    a, b = domain.of(Interval)
    assert domain.is_closed
    return All[x:Interval(a, b)](GreaterEqual(fx, fx._subs(x, a)))


@prove
def prove(Eq):
    from axiom import algebra, sets, calculus

    a, b, x = Symbol(real=True)
    domain = Interval(a, b)
    f = Function(real=True)
    Eq << apply(All[x:domain](Derivative[x](f(x)) >= 0))

    Eq << algebra.cond.of.et.infer.split.apply(Eq[1], cond=a < b)

    Eq << Eq[-1].this.rhs.apply(algebra.all.of.infer)

    Eq << Eq[-1].this.apply(algebra.infer.flatten)

    Eq << Eq[-1].this.lhs.apply(sets.ge.el.then.eq)

    Eq << algebra.infer.of.infer.subs.apply(Eq[-1])

    Eq << algebra.cond.then.infer.apply(Eq[0], cond=a < b)

    Eq << algebra.infer_et.then.infer.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(calculus.lt.all_ge_zero.then.all.ge.monotony.right_close)




if __name__ == '__main__':
    run()
# created on 2023-10-03
