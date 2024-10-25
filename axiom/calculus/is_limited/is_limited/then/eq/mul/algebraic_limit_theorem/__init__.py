from util import *


@apply
def apply(limited_f, limited_g):
    from axiom.calculus.is_limited.then.any.all.limit_definition import of_limited
    fx, limit = of_limited(limited_f, real=True)
    x, x0 = limit

    gx, S[limit] = of_limited(limited_g, real=True)

    return Equal(Limit[x:x0](fx * gx), limited_f.lhs * limited_g.lhs)


@prove
def prove(Eq):
    from axiom import calculus, sets, algebra

    x, x0 = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Element(Limit[x:x0 + S.Infinitesimal](f(x)), Reals), Element(Limit[x:x0 + S.Infinitesimal](g(x)), Reals))

    is_zero = And(Equal(Eq[0].lhs, 0), Eq[1])
    Eq << Infer(is_zero, is_zero, plausible=True)

    Eq.is_zero = Eq[-1].this.rhs.apply(calculus.is_zero.is_limited.then.is_zero.limit.algebraic_limit_theorem)

    Eq << Eq[-1].this.rhs.args[1].apply(sets.el.then.any.eq, var='B', simplify=None)

    Eq << Eq[-1].this.rhs.apply(algebra.cond.any.then.any.et, simplify=None)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.eq.eq.then.eq.mul)

    Eq << algebra.infer.infer.then.infer.et.apply(Eq.is_zero, Eq[-1])

    Eq.mul_is_zero = Eq[-1].this.rhs.apply(algebra.eq.eq.then.eq.trans, reverse=True)

    is_nonzero = And(Element(Eq[0].lhs, Reals - {0}), Eq[1])
    Eq << Infer(is_nonzero, is_nonzero, plausible=True)

    Eq << Eq[-1].this.rhs.apply(calculus.is_limited.is_limited.then.eq.mul.nonzero.algebraic_limit_theorem)

    Eq << algebra.infer.infer.then.infer.ou.apply(Eq.mul_is_zero, Eq[-1])

    Eq << Eq[-1].this.find(Equal[0]).apply(sets.eq.of.el)

    Eq <<= Eq[0] & Eq[1]

    Eq << algebra.cond.infer.then.cond.trans.apply(Eq[-1], Eq[-2])




if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Limit_of_a_function# Properties

# created on 2020-04-17
# updated on 2023-05-18
from . import st
