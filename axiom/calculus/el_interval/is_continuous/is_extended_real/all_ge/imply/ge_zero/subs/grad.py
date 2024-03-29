from util import *


@apply
def apply(el_interval, is_continuous, is_extended_real, all_ge):
    from axiom.calculus.lt.is_continuous.is_differentiable.eq.imply.any.eq.Rolle import of_continuous
    fx, limit = of_continuous(is_continuous)
    x, a, b = limit

    from axiom.calculus.lt.is_continuous.is_extended_real.is_extended_real.eq.imply.any.le.Rolle import is_differentiable_at
    S[fx], S[limit] = is_differentiable_at(is_extended_real)

    c, S[Interval.open(a, b)] = el_interval.of(Element)
    (S[fx], S[fx._subs(x, c)]), S[limit] = all_ge.of(All[GreaterEqual])
    return Subs[x:c](Derivative[x + S.Infinitesimal](fx)) >= 0


@prove
def prove(Eq):
    from axiom import calculus, sets

    a, b, x, c = Symbol(real=True)
    f = Function(shape=(), real=True)
    from axiom.calculus.all_eq.imply.all.any.eq.intermediate_value_theorem import is_continuous
    Eq << apply(
        Element(c, Interval.open(a, b)),
        is_continuous(f, a, b),
        All[x:a:b](Element(Derivative[x + S.Infinitesimal](f(x)), ExtendedReals)),
        All[x:a:b](f(x) >= f(c)))

    @Function
    def g(x):
        return -f(x)
    Eq.g_def = g(x).this.defun()
    
    Eq << -Eq.g_def.reversed
    
    ξ = Eq[1].variable
    Eq <<= Eq[1].subs(Eq[-1], Eq[-1].subs(x, ξ)), Eq[2].subs(Eq[-1]), Eq[3].subs(Eq[-1], Eq[-1].subs(x, c))
    
    Eq <<= Eq[-3].this.expr.lhs.apply(calculus.limit.to.mul),\
        Eq[-2].this.expr.lhs.apply(calculus.grad.to.mul, simplify=None),\
        -Eq[-1].this.expr
    
    Eq << Eq[-2].this.expr.apply(sets.el.imply.el.neg, simplify=None)
    
    Eq << calculus.el_interval.is_continuous.is_extended_real.all_le.imply.le_zero.subs.grad.apply(Eq[0], Eq[-4], Eq[-1], Eq[-2])
    
    Eq << Eq[-1].subs(Eq.g_def)
    
    Eq << Eq[-1].this.find(Derivative).apply(calculus.grad.to.mul)
    
    Eq << -Eq[-1]


if __name__ == '__main__':
    run()
# created on 2023-11-10
