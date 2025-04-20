from util import *


@apply
def apply(limited_f, limited_g):
    from Axiom.Calculus.Any.All.of.IsLimited.limit_definition import of_limited
    fx, limit = of_limited(limited_f, real=True)
    x, x0 = limit

    gx, S[limit] = of_limited(limited_g, real=True)

    return Equal(Limit[x:x0](fx * gx), limited_f.lhs * limited_g.lhs)


@prove
def prove(Eq):
    from Axiom import Calculus, Set, Algebra, Logic

    x, x0 = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Element(Limit[x:x0 + S.Infinitesimal](f(x)), Reals), Element(Limit[x:x0 + S.Infinitesimal](g(x)), Reals))

    is_zero = And(Equal(Eq[0].lhs, 0), Eq[1])
    Eq << Imply(is_zero, is_zero, plausible=True)

    Eq.is_zero = Eq[-1].this.rhs.apply(Calculus.Eq_0.Limit.of.Eq_0.IsLimited.algebraic_limit_theorem)

    Eq << Eq[-1].this.rhs.args[1].apply(Set.Any.Eq.of.Mem, var='B', simplify=None)

    Eq << Eq[-1].this.rhs.apply(Algebra.Any.And.of.Cond.Any, simplify=None)

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.EqMul.of.Eq.Eq)

    Eq << Logic.ImpAndS.of.Imp.Imp.apply(Eq.is_zero, Eq[-1])

    Eq.mul_is_zero = Eq[-1].this.rhs.apply(Algebra.Eq.of.Eq.Eq, reverse=True)

    is_nonzero = And(Element(Eq[0].lhs, Reals - {0}), Eq[1])
    Eq << Imply(is_nonzero, is_nonzero, plausible=True)

    Eq << Eq[-1].this.rhs.apply(Calculus.EqMul.of.IsLimited.IsLimited.nonzero.algebraic_limit_theorem)

    Eq << Logic.ImpOrS.of.Imp.Imp.apply(Eq.mul_is_zero, Eq[-1])

    Eq << Eq[-1].this.find(Equal[0]).apply(Set.Eq.given.Mem)

    Eq <<= Eq[0] & Eq[1]

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[-1], Eq[-2])




if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Limit_of_a_function# Properties

# created on 2020-04-17
# updated on 2023-05-18

