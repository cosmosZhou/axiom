from util import *


@apply
def apply(is_positive, eq):
    den = is_positive.of(Expr > 0)
    lhs, rhs = eq.of(Equal)
    assert den == lhs or den == rhs

    return Equal(log(lhs), log(rhs))


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True)
    f, g = Function(shape=(), real=True)
    Eq << apply(f(x) > 0, Equal(f(x), g(x)))

    Eq << Eq[-1].subs(Eq[1])

    Eq << Algebra.And.given.And.apply(Eq[-1])

    Eq << Eq[0].subs(Eq[1])

    Eq << Algebra.Ne.of.Gt.apply(Eq[-1])

    Eq << Algebra.Ne.of.Gt.apply(Eq[0])

    


if __name__ == '__main__':
    run()
# created on 2019-08-08
# updated on 2025-04-20
