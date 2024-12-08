from util import *


@apply
def apply(is_zero, x=None):
    from Axiom.Algebra.Add.eq.Zero.to.And_Imply_Or_EqS.cubic import cubic_coefficient
    fx = is_zero.of(Equal[0])
    S[1], S[0], p, q = cubic_coefficient(fx, x=x)

    delta = 4 * p ** 3 / 27 + q ** 2
    U = sqrt(delta) - q
    V = -sqrt(delta) - q

    A = (sqrt(delta) / 2 - q / 2) ** (S.One / 3)
    B = (-sqrt(delta) / 2 - q / 2) ** (S.One / 3)

    w = -S.One / 2 + S.ImaginaryUnit * sqrt(3) / 2
    arg_p = Ceiling(3 * Arg(-p / 3) / (S.Pi * 2) - S.One / 2)
    # arg_AB = Ceiling(3 * Arg(A * B) / (S.Pi * 2) - S.One / 2)

    arg_AB = Piecewise((0, Equal(p * Ceiling((Arg(U) + Arg(V)) / (2 * S.Pi) - S.One / 2), 0)), (1, Arg(U) + Arg(V) > S.Pi), (-1, True))

    d = arg_p - arg_AB
    return Imply(Equal(d, 0), Equal(x, A + B) | Equal(x, A * w + B * ~w) | Equal(x, A * ~w + B * w)), Imply(Equal(d % 3, 1), Equal(x, A * w + B) | Equal(x, A * ~w + B * ~w) | Equal(x, A + B * w)), Imply(Equal(d % 3, 2), Equal(x, A * ~w + B) | Equal(x, A + B * ~w) | Equal(x, A * w + B * w))



@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x, p, q = Symbol(complex=True, given=True)
    Eq << apply(Equal(x ** 3 + p * x + q, 0), x=x)

    Eq << Sets.Arg.el.Lopen_.NegPi.Pi.apply(-p)

    Eq << Sets.In.to.In.Mul.Interval.apply(Eq[-1], 3, simplify=None)

    Eq << Sets.In.to.In.Sub.apply(Eq[-1], S.Pi, simplify=None)

    Eq << Sets.In.to.In.Div.Interval.apply(Eq[-1], S.Pi * 2, simplify=None)

    Eq << Sets.In_Interval.to.In_Range.Ceiling.apply(Eq[-1])

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.rhs.apply(Sets.Range.eq.FiniteSet)

    Eq << Sets.Piece.el.FiniteSet.apply(Eq[1].find(Piecewise))

    Eq << Sets.In.to.In.Neg.apply(Eq[-1])

    Eq << Sets.In.In.to.In.Add.FiniteSet.apply(Eq[-1], Eq[-3])

    V = Eq[-1].find(Arg[Add]).arg
    U = Eq[-1].find(Arg[2]).arg
    Eq.eq_peicewise = Algebra.Ceiling.Arg.eq.Piece.apply(Eq[-1].find(Ceiling)._subs(-p, U ** (S.One / 3) * V ** (S.One / 3)))

    Eq << Eq[-1].subs(Eq.eq_peicewise.reversed)

    Eq.ou = Sets.In_FiniteSet.to.Or.Eq.apply(Eq[-1])

    Eq <<= Eq.ou & Eq[0]

    Eq << Algebra.And.to.Or.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Equal[-2] & Equal[0]).apply(Algebra.Eq_.Add.Zero.Eq_Ceiling.to.Or.Eq.cubic, x, ret=0)

    Eq << Eq[-1].this.find(Equal[-1] & Equal[0]).apply(Algebra.Eq_.Add.Zero.Eq_Ceiling.to.Or.Eq.cubic, x, ret=0)

    Eq << Eq[-1].this.find(Equal[0] & Equal[0]).apply(Algebra.Eq_.Add.Zero.Eq_Ceiling.to.Or.Eq.cubic, x, ret=0)

    Eq << Eq[-1].this.find(Equal[S(1)] & Equal[0]).apply(Algebra.Eq_.Add.Zero.Eq_Ceiling.to.Or.Eq.cubic, x, ret=0)

    Eq << Eq[-1].this.find(Equal[S(2)] & Equal[0]).apply(Algebra.Eq_.Add.Zero.Eq_Ceiling.to.Or.Eq.cubic, x, ret=0)

    # find Equal[S(1)] & Equal[S(-2)]
    Eq << Eq[-1].this.args[:3:2].apply(Algebra.Or.to.And.collect)

    # find Equal[S(-1)] & Equal[S(2)]
    Eq << Eq[-1].this.args[:2].apply(Algebra.Or.to.And.collect)

    Eq << Eq[-1].this.find(Equal[Integer] | Equal[Integer]).apply(Algebra.Or_Eq.to.Eq.Mod)

    Eq << Eq[-1].this.find(Equal[Integer] | Equal[Integer]).apply(Algebra.Or_Eq.to.Eq.Mod)

    Eq << Eq[-1].this.find(Equal[Ceiling, Ceiling]).apply(Algebra.Eq.to.Eq_0.Mod, 3, swap=True)

    Eq << Eq[-1].subs(Eq.eq_peicewise)

    Eq << Algebra.Or.to.And.Imply.apply(Eq[-1])

    Eq << Eq[1].this.lhs.apply(Algebra.Eq.to.Eq_0.Mod, 3)


if __name__ == '__main__':
    run()
# created on 2018-11-24
# updated on 2023-05-15

