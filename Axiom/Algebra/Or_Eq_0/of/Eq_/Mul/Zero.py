from util import *


@apply
def apply(given):
    eqs = given.of(Or)

    args = []
    for eq in eqs:
        args.append(eq.of(Equal[0]))

    return Equal(Mul(*args), 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    a, b = Symbol(real=True, given=True)
    Eq << apply(Equal(a, 0) | Equal(b, 0))

    Eq << ~Eq[0]

    Eq <<= Eq[-1] & Eq[1]

    Eq << Iff(Equal(Bool(Unequal(a, 0) & Equal(a * b, 0)), 1) & Unequal(b, 0),
                     Eq[-1], plausible=True)

    Eq << Eq[-1].this.find(Bool).apply(Algebra.Bool.eq.Piece)

    Eq << Iff(Unequal(a, 0) & Equal(a * b, 0),
                     Unequal(a, 0) & Equal(b, 0), plausible=True)

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(Algebra.Ne_0.Eq.to.Eq.Div)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ne_0.Eq.to.Eq.Mul)

    Eq << Algebra.Iff.to.Eq.apply(Eq[-3])

    Eq << Eq[4].subs(Eq[-1])

    Eq << Eq[-1].this.find(Bool).apply(Algebra.Bool.eq.Piece)

    Eq << Eq[-1].subs(Eq[1])


if __name__ == '__main__':
    run()

# created on 2018-01-29
