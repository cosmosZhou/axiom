from util import *


@apply
def apply(el, all_le):
    lim, R = el.of(Element)
    fx, (x, x0) = lim.of(Limit)
    x0, epsilon = x0.clear_infinitesimal()
    assert epsilon
    assert R in Reals
    S[fx], (x, *cond) = all_le.of(All[Expr >= 0])
    if epsilon > 0:
        S[x0], delta = cond
        delta -= x0
        assert delta > 0
    else:
        delta, S[x0] = cond
        delta -= x0
        assert delta < 0
    return lim >= 0


@prove
def prove(Eq):
    from axiom import calculus, sets

    x = Symbol(real=True)
    x0 = Symbol(real=True, given=True)
    delta = Symbol(real=True, given=True, positive=True)
    f = Function(real=True)
    Eq << apply(
        Element(Limit[x:x0 - S.Infinitesimal](f(x)), Reals),
        All[x:x0 - delta:x0](f(x) >= 0))

    @Function
    def g(x):
        return -f(x)
    Eq.g_def = g(x).this.defun()

    Eq << -Eq.g_def.reversed

    Eq <<= Eq[0].subs(Eq[-1]), Eq[1].subs(Eq[-1])

    Eq <<= Eq[-2].this.lhs.apply(calculus.limit.to.mul), -Eq[-1].this.expr

    Eq << sets.el.imply.el.neg.apply(Eq[-2])

    Eq << calculus.is_real.all_le.imply.le_zero.limit.one_sided.apply(*Eq[-2:])

    Eq << Eq[-1].subs(Eq.g_def)

    Eq << -Eq[-1].this.lhs.apply(calculus.limit.to.mul)

    


if __name__ == '__main__':
    run()
# created on 2023-10-15
