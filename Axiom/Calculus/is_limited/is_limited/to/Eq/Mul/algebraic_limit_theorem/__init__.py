from util import *


@apply
def apply(limited_f, limited_g):
    from Axiom.Calculus.is_limited.to.Any.All.limit_definition import of_limited
    fx, limit = of_limited(limited_f, real=True)
    x, x0 = limit

    gx, S[limit] = of_limited(limited_g, real=True)

    return Equal(Limit[x:x0](fx * gx), limited_f.lhs * limited_g.lhs)


@prove
def prove(Eq):
    from Axiom import Calculus, Sets, Algebra

    x, x0 = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Element(Limit[x:x0 + S.Infinitesimal](f(x)), Reals), Element(Limit[x:x0 + S.Infinitesimal](g(x)), Reals))

    is_zero = And(Equal(Eq[0].lhs, 0), Eq[1])
    Eq << Imply(is_zero, is_zero, plausible=True)

    Eq.is_zero = Eq[-1].this.rhs.apply(Calculus.Eq_0.is_limited.to.Eq_0.Limit.algebraic_limit_theorem)

    Eq << Eq[-1].this.rhs.args[1].apply(Sets.In.to.Any.Eq, var='B', simplify=None)

    Eq << Eq[-1].this.rhs.apply(Algebra.Cond.Any.to.Any.And, simplify=None)

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.Eq.Eq.to.Eq.Mul)

    Eq << Algebra.Imply.Imply.to.Imply.And.apply(Eq.is_zero, Eq[-1])

    Eq.mul_is_zero = Eq[-1].this.rhs.apply(Algebra.Eq.Eq.to.Eq.trans, reverse=True)

    is_nonzero = And(Element(Eq[0].lhs, Reals - {0}), Eq[1])
    Eq << Imply(is_nonzero, is_nonzero, plausible=True)

    Eq << Eq[-1].this.rhs.apply(Calculus.is_limited.is_limited.to.Eq.Mul.nonzero.algebraic_limit_theorem)

    Eq << Algebra.Imply.Imply.to.Imply.Or.apply(Eq.mul_is_zero, Eq[-1])

    Eq << Eq[-1].this.find(Equal[0]).apply(Sets.Eq.of.In)

    Eq <<= Eq[0] & Eq[1]

    Eq << Algebra.Cond.Imply.to.Cond.trans.apply(Eq[-1], Eq[-2])




if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Limit_of_a_function# Properties

# created on 2020-04-17
# updated on 2023-05-18
from . import st
