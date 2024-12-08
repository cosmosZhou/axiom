from util import *


@apply
def apply(limited_f, limited_g):
    from Axiom.Calculus.is_limited.to.Any.All.limit_definition import of_limited
    fx, (x, x0) = of_limited(limited_f, real=True)
    gx, S[(x, x0)] = of_limited(limited_g, real=True)

    return Equal(Limit[x:x0](fx - gx), limited_f.lhs - limited_g.lhs)


@prove
def prove(Eq):
    from Axiom import Calculus, Algebra

    x = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Element(Limit[x:oo](f(x)), Reals), Element(Limit[x:oo](g(x)), Reals))

    ε, N = Symbol(real=True, positive=True)
    ε_0 = Symbol(real=True, positive=True)
    N0 = Symbol('N_0', real=True, positive=True)
    Eq << Calculus.is_limited.to.Any.All.limit_definition.symbol_subs.apply(Eq[0], ε_0, N0, var='A')

    Eq << Eq[-1].subs(ε_0, ε / 2)

    ε_1 = Symbol(real=True, positive=True)
    N1 = Symbol('N_1', real=True, positive=True)
    Eq << Calculus.is_limited.to.Any.All.limit_definition.symbol_subs.apply(Eq[1], ε_1, N1, var='B')

    Eq << Eq[-1].subs(ε_1, ε / 2)

    Eq << Algebra.Any_All.Any_All.to.Any.All.And.limits_Intersect.apply(Eq[-1], Eq[-3])

    Eq << Eq[-1].this.expr.expr.apply(Algebra.Lt.Lt.to.Lt.Abs.Sub)

    Eq << Algebra.Any.to.Any.subs.apply(Eq[-1], Max(N0, N1), N)

    Eq << Calculus.Any_All.to.Eq.limit_definition.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.args[0].definition

    Eq << Eq[-1].this.rhs.args[0].args[1].definition




if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Limit_of_a_function# Properties

# created on 2020-05-18
# updated on 2023-05-06
