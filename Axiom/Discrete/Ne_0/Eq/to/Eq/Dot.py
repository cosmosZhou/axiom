from util import *


@apply
def apply(unequality, equality):
    divisor = unequality.of(Unequal[Determinant, 0])
    lhs, rhs = equality.of(Equal)
    return Equal(lhs @ Inverse(divisor), rhs @ Inverse(divisor))


@prove
def prove(Eq):
    from Axiom import Discrete, Algebra
    n = Symbol(integer=True)
    A = Symbol(real=True, shape=(n, n))
    a, b = Symbol(real=True, shape=(n,))
    Eq << apply(Unequal(Determinant(A), 0), Equal(a @ A, b))

    Eq << Eq[1] @ Cofactors(A).T

    Eq << Discrete.Dot.eq.Mul.adjugate.apply(A)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Algebra.Ne_0.Eq.to.Eq.scalar.apply(Eq[0], Eq[-1])

    Eq << Discrete.Ne_0.to.Eq.Det.apply(Eq[0]) * Determinant(A)

    Eq << Eq[-2].subs(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-02-12
