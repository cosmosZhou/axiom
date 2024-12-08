from util import *


@apply
def apply(is_zero, x=None, d=0):
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
    arg_AB = Piecewise((0, Equal(p * Ceiling((Arg(U) + Arg(V)) / (2 * S.Pi) - S.One / 2), 0)), (1, Arg(U) + Arg(V) > S.Pi), (-1, True))

    if d == 0:
        x0 = A + B
    elif d == 1:
        x0 = A * w + B
    elif d == 2:
        x0 = A * ~w + B
    else:
        ...

    return Equal((arg_p - arg_AB) % 3, d), Equal(x, x0)



@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x, p, q = Symbol(complex=True, given=True)
    Eq << apply(Equal(x ** 3 + p * x + q, 0), x=x, d=1)

    Eq << Sets.Arg.el.Lopen_.NegPi.Pi.apply(-p)

    Eq << Sets.In.to.In.Div.Interval.apply(Eq[-1], 2 * S.Pi / 3)

    Eq << Sets.In.to.In.Sub.apply(Eq[-1], S.One / 2)

    Eq << Sets.In_Interval.to.In_Range.Ceiling.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Sets.Range.eq.FiniteSet)

    Eq << Sets.Piece.el.FiniteSet.apply(Eq[1].find(Piecewise))

    Eq << Sets.In.to.In.Neg.apply(Eq[-1])

    Eq << Sets.In.In.to.In.Add.FiniteSet.apply(Eq[-1], Eq[-3])

    Eq.contains = Sets.Eq_Mod.In.to.In.sift.apply(Eq[1], Eq[-1])

    Eq <<= Eq[0].cond.this.apply(Algebra.Eq_.Add.Zero.of.And.Eq.cubic.depressed, x, 1), Eq[0].cond.this.apply(Algebra.Eq_.Add.Zero.of.And.Eq.cubic.depressed, x, -2)

    Eq <<= Algebra.Cond.Cond.to.Cond.subs.apply(Eq[2], Eq[-2]) & Algebra.Cond.Cond.to.Cond.subs.apply(Eq[2], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Sets.Or_Eq.of.In.FiniteSet)
    Eq << Algebra.Cond.Given.to.Cond.trans.apply(Eq.contains, Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-11-20
