from util import *


@apply
def apply(el, all_le):
    lim, R = el.of(Element)
    fx, (x, x0) = lim.of(Limit)
    assert R in Reals
    S[fx], (x, cond) = all_le.of(All[Expr <= 0])
    diff, (delta, S[diff]) = cond.of((Abs > 0) & (Expr > Abs))
    S[x0] = x - diff
    assert delta > 0
    return lim <= 0


@prove
def prove(Eq):
    from axiom import calculus, algebra

    x = Symbol(real=True)
    x0 = Symbol(real=True, given=True)
    delta = Symbol(real=True, given=True, positive=True)
    f = Function(real=True)
    Eq << apply(
        Element(Limit[x:x0](f(x)), Reals),
        All[x:(abs(x - x0) > 0) & (delta > abs(x - x0))](f(x) <= 0))

    Eq << ~Eq[2]

    A = Symbol(Eq[-1].lhs)
    Eq << A.this.definition.reversed

    Eq << Eq[-2].subs(Eq[-1])

    δ_quote = Symbol(real=True, positive=True)
    Eq << calculus.gt_zero.eq_limit.then.any.all.gt.apply(*Eq[-2:], delta=δ_quote)

    Eq << algebra.cond.any_all.then.any.all.et.apply(Eq[-2] / 2, Eq[-1])

    Eq << Eq[-1].this.find(And).apply(algebra.gt.gt.then.gt.trans)

    Eq << Eq[-1].this.find(Less).reversed

    Eq << Eq[-1].this.find(And[~Greater]).apply(algebra.gt.of.gt.relax, lower=Min(δ_quote, delta))

    Eq << Eq[1].this.find(And[~Greater]).apply(algebra.gt.of.gt.relax, lower=Min(δ_quote, delta))

    Eq << algebra.cond.any.then.any.et.apply(*Eq[-2:], simplify=None)

    Eq << Eq[-1].subs(x, x0 + Min(δ_quote, delta) / 2)




if __name__ == '__main__':
    run()
# created on 2023-10-15
from . import one_sided
