from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal)
    lhs = lhs.of(Bool)
    rhs = rhs.of(Bool)
    return Iff(lhs, rhs)


@prove
def prove(Eq):
    from Axiom import Algebra
    a, b = Symbol(integer=True)
    f = Function(shape=())

    Eq << apply(Equal(Bool(a > b), Bool(f(a) > f(b))))

    Eq << Eq[0] * Eq[0].lhs

    Eq << Algebra.Square.eq.Bool.apply(Eq[-1].lhs)

    Eq << Eq[-2] - Eq[-1]

    Eq << Algebra.Eq_0.to.Eq.apply(Eq[-1])

    Eq.suffice = Algebra.Eq.to.Imply.Bool.apply(Eq[-1])

    Eq << Eq[0] * Eq[0].rhs

    Eq << Algebra.Square.eq.Bool.apply(Eq[0].rhs ** 2)

    Eq << Eq[-2] + Eq[-1]

    Eq << Eq[-1].this.apply(Algebra.Eq.simp.terms.common)

    Eq << Algebra.Eq.to.Imply.Bool.apply(Eq[-1])

    Eq <<= Eq.suffice & Eq[-1]


if __name__ == '__main__':
    run()

# created on 2018-03-22
