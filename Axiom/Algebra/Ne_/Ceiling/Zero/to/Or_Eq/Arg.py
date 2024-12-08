from util import *


@apply
def apply(is_nonzero):
    ceiling = is_nonzero.of(Unequal[0])
    ((A, B), S[S.One / (S.Pi * 2)]), S[S.One  / 2] = ceiling.of(Ceiling[(Arg + Arg) * Expr - Expr])
    return Equal(ceiling, 1) | Equal(ceiling, -1)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    A, B = Symbol(complex=True, given=True)
    Eq << apply(Unequal(Ceiling((Arg(A) + Arg(B)) / (S.Pi * 2) - S.One / 2), 0))

    Eq <<= Sets.Arg.el.Lopen_.NegPi.Pi.apply(A), Sets.Arg.el.Lopen_.NegPi.Pi.apply(B)

    Eq << Sets.In.In.to.In.Add.Interval.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << Sets.In.to.In.Div.Interval.apply(Eq[-1], S.Pi * 2)

    Eq << Sets.In.to.In.Sub.apply(Eq[-1], S.One / 2)

    Eq << Sets.In_Interval.to.In_Range.Ceiling.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Sets.Range.eq.FiniteSet)

    Eq << Sets.In_FiniteSet.to.Or.Eq.apply(Eq[-1])

    Eq << Algebra.Cond.Or.to.Cond.apply(Eq[0], Eq[-1])




if __name__ == '__main__':
    run()
# created on 2018-10-24
