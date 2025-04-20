from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(Any[Unequal])
    return Unequal(Lamda(lhs, *limits), Lamda(rhs, *limits))


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True, positive=True, given=True)
    i = Symbol(integer=True)
    f, g = Function(real=True)
    Eq << apply(Any[i:n](Unequal(f(i), g(i))))

    Eq << ~Eq[1]

    Eq << Algebra.Eq_0.of.Eq.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Add.eq.Lamda)

    Eq << Algebra.All_Eq_0.of.Lamda.eq.Zero.apply(Eq[-1])
    Eq << Eq[-1].this.expr.apply(Algebra.Eq.of.Sub.eq.Zero)

    Eq << ~Eq[-1]




if __name__ == '__main__':
    run()
# created on 2022-01-01
