from util import *


@apply
def apply(is_nonzero, eq, x=None):
    from Axiom.Algebra.Le.Ge.to.Le.quadratic import quadratic_coefficient
    a = is_nonzero.of(Unequal[0])
    fx, rhs = eq.of(Equal)
    if not rhs.is_Zero:
        fx -= rhs

    x, S[a], S[0], c = quadratic_coefficient(fx, x=x)
    delta = -4 * a * c

    return Or(Equal(x, sqrt(delta) / (a * 2)), Equal(x, -sqrt(delta) / (a * 2)))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a, c = Symbol(complex=True)
    Eq << apply(Unequal(a, 0), Equal(a * x ** 2 + c, 0), x=x)

    Eq << Eq[1] - c

    Eq << Algebra.Ne_0.Eq.to.Eq.scalar.apply(Eq[0], Eq[-1])

    t = Symbol(sqrt(Eq[-1].rhs))
    Eq << t.this.definition

    Eq.t_squared = Eq[-1] ** 2

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq[-2], Eq.t_squared)

    Eq << Eq[-1] - Eq[-1].rhs

    Eq << Eq[-1].this.lhs.factor()

    Eq << Algebra.Mul.eq.Zero.to.OrEqS_0.apply(Eq[-1])

    Eq << Eq[-1].this.args[0].reversed

    Eq.ou = Eq[-1].this.args[1] - t

    Eq << -Eq.t_squared * a

    Eq << Eq[-1].reversed

    Eq << Eq[2].subs(Eq[-1])

    Eq << sqrt(a * a * t * t).this.simplify()

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Algebra.Or.of.And.collect.apply(Eq[-1])

    Eq << Algebra.Or.of.Eq.Abs.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.eq.Abs)

    Eq << Algebra.Or.to.Eq.Abs.apply(Eq.ou)





if __name__ == '__main__':
    run()
# created on 2018-08-15
# updated on 2023-06-26
