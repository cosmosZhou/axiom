from util import *


@apply
def apply(el_Interval, is_continuous, is_extended_real, all_ge):
    from Axiom.Calculus.Lt.is_continuous.is_differentiable.Eq.to.Any.Eq.Rolle import of_continuous
    fx, limit = of_continuous(is_continuous)
    x, a, b = limit

    from Axiom.Calculus.Lt.is_continuous.is_extended_real.is_extended_real.Eq.to.Any.Le.Rolle import is_differentiable_at
    S[fx], S[limit] = is_differentiable_at(is_extended_real, -1)

    c, S[Interval.open(a, b)] = el_Interval.of(Element)
    (S[fx], S[fx._subs(x, c)]), S[limit] = all_ge.of(All[GreaterEqual])
    return Subs[x:c](Derivative[x - S.Infinitesimal](fx)) <= 0


@prove
def prove(Eq):
    from Axiom import Calculus, Sets

    a, b, x, c = Symbol(real=True)
    f = Function(shape=(), real=True)
    from Axiom.Calculus.All_Eq.to.All.Any.Eq.intermediate_value_theorem import is_continuous
    Eq << apply(
        Element(c, Interval.open(a, b)),
        is_continuous(f, a, b),
        All[x:a:b](Element(Derivative[x - S.Infinitesimal](f(x)), ExtendedReals)),
        All[x:a:b](f(x) >= f(c)))

    @Function
    def g(x):
        return -f(x)
    Eq.g_def = g(x).this.defun()

    Eq << -Eq.g_def.reversed

    ξ = Eq[1].variable
    Eq <<= Eq[1].subs(Eq[-1], Eq[-1].subs(x, ξ)), Eq[2].subs(Eq[-1]), Eq[3].subs(Eq[-1], Eq[-1].subs(x, c))

    Eq <<= Eq[-3].this.expr.lhs.apply(Calculus.Limit.eq.Mul),\
        Eq[-2].this.expr.lhs.apply(Calculus.Grad.eq.Mul, simplify=None),\
        -Eq[-1].this.expr

    Eq << Eq[-2].this.expr.apply(Sets.In.to.In.Neg, simplify=None)

    Eq << Calculus.In_Interval.is_continuous.is_extended_real.All_Le.to.Ge_0.Subs.Grad.apply(Eq[0], Eq[-4], Eq[-1], Eq[-2])

    Eq << Eq[-1].subs(Eq.g_def)

    Eq << Eq[-1].this.find(Derivative).apply(Calculus.Grad.eq.Mul)

    Eq << -Eq[-1]




if __name__ == '__main__':
    run()
# created on 2023-11-10
