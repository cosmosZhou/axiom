from util import *


@apply
def apply(is_nonzero, q):
    p = is_nonzero.of(Unequal[0])

    delta = 4 * p ** 3 / 27 + q ** 2

    U = sqrt(delta) - q
    V = -sqrt(delta) - q

    return Equal(Ceiling(3 * Arg(U ** (S.One / 3) * V ** (S.One / 3)) / (S.Pi * 2) - S.One / 2), Piecewise((0, Equal(Ceiling((Arg(U) + Arg(V)) / (2 * S.Pi) - S.One / 2), 0)), (1, Arg(U) + Arg(V) > S.Pi), (-1, True)))


@prove
def prove(Eq):
    from Axiom import Algebra, Geometry, Sets

    p, q = Symbol(complex=True, given=True)
    Eq << apply(Unequal(p, 0), q)

    delta = 4 * p ** 3 / 27 + q ** 2
    U = Symbol(sqrt(delta) - q)
    V = Symbol(-sqrt(delta) - q)
    Eq.U, Eq.V = U.this.definition, V.this.definition

    Eq << Eq.U * Eq.V

    Eq.UV = Eq[-1].this.rhs.apply(Algebra.Mul.eq.Add, deep=True)

    Eq << Eq[1].subs(Eq.U.reversed, Eq.V.reversed)

    Eq << Eq[-1].this.find(Arg[~Mul[Pow]]).apply(Algebra.Mul.Root.eq.Mul.Piece.cubic_root)

    Eq << Eq[-1].subs(Eq.UV)

    Eq << Eq[-1].this.find(Mul[Piecewise]).apply(Algebra.Mul.eq.Piece)

    Eq << Eq[-1].this.find(Arg[Piecewise]).apply(Algebra.Arg.Piece.eq.Piece)

    Eq << Eq[-1].this.find(Mul[Piecewise]).apply(Algebra.Mul.eq.Piece)

    Eq << Eq[-1].this.find(Add[Piecewise]).apply(Algebra.Add.eq.Piece)

    Eq << Eq[-1].this.find(Ceiling[Piecewise]).apply(Algebra.Ceiling.Piece.eq.Piece)

    Eq.eq = Eq[-1].this.find(Ceiling[~Mul]).apply(Algebra.Mul.eq.Add)

    Eq << Or(*Eq[-1].find(Or).args[:2]).this.apply(Algebra.Or.to.Eq_0)

    Eq << Eq[-1].subs(Eq.UV)

    Eq << Eq[-1].this.rhs * (-Integer(27) / 4)

    Eq.suffice = Eq[-1].this.rhs.apply(Algebra.Eq_.Pow.Zero.to.Eq_0)

    Eq << Equal(U * V, 0).this.apply(Algebra.Mul.eq.Zero.to.OrEqS_0)

    Eq << Eq[-1].subs(Eq.UV)

    Eq << Eq[-1].this.lhs * (-Integer(27) / 4)

    Eq << Eq[-1].this.lhs.apply(Algebra.Eq_.Pow.Zero.of.Eq_0)

    Eq <<= Eq.suffice & Eq[-1]

    Eq << Algebra.Cond.of.Cond.subs.Cond.apply(Eq.eq, old=Eq[-1].lhs, new=Eq[-1].rhs)

    Eq << Algebra.Cond.of.Cond.subs.Bool.apply(Eq[-1], cond=Eq[0], invert=True)

    Eq.p_cubic = Eq[-1].find(Pow[Mul]).this.apply(Algebra.Root.eq.Mul.ExpI.Arg)

    Eq.p_is_positive = Algebra.Ne_0.to.Gt_0.Abs.apply(Eq[0])

    Eq << Algebra.Gt_0.to.Eq.Arg.apply(Eq.p_is_positive, Eq.p_cubic.find(Exp))

    Eq << Algebra.Eq.to.Eq.Arg.apply(Eq.p_cubic)

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.rhs.apply(Algebra.Arg.ExpI.eq.Mul.Arg)

    Eq << Eq[-1].this.find(Arg[Mul]).apply(Algebra.Arg.Mul.eq.Add.st.Pow)

    Eq << Eq[-6].subs(Eq[-1])

    Eq.eq_simplified = Eq[-1].this.find(Ceiling[Add[~Mul[Add]]]).apply(Algebra.Mul.eq.Add)

    Eq << Eq.p_cubic * exp(S.ImaginaryUnit * 2 * S.Pi / 3)

    Eq << Algebra.Gt_0.to.Eq.Arg.apply(Eq.p_is_positive, Mul(*Eq[-1].rhs.args[1:]))

    Eq << Algebra.Eq.to.Eq.Arg.apply(Eq[-2])

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.rhs.arg.apply(Algebra.Mul.eq.Exp)

    Eq.arg_p3_w = Eq[-1].this.lhs.find(Exp).apply(Geometry.ExpI.eq.Add.Euler)

    Eq.p3_contains = Sets.Arg.el.Lopen_.NegPi.Pi.apply(-p ** 3)

    Eq << Sets.In.to.In.Add.apply(Eq.p3_contains, S.Pi * 2, simplify=None)

    Eq << Sets.In.to.In.Div.Interval.apply(Eq[-1], 3, simplify=None)

    Eq << Sets.In.to.Eq.Arg.ExpI.apply(Eq[-1])

    Eq << Eq.arg_p3_w.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Arg[Mul]).apply(Algebra.Arg.Mul.eq.Add.st.Pow)

    Eq << Eq.eq_simplified.subs(Eq[-1])

    Eq << Eq[-1].this.find(ExprCondPair[Ceiling[Add[~Mul[Add]]]]).apply(Algebra.Mul.eq.Add)

    Eq.eq_simplified = Eq[-1].this.find(Add[~Ceiling]).apply(Algebra.Ceiling.eq.Add.half)

    Eq << Eq.p_cubic * exp(-S.ImaginaryUnit * 2 * S.Pi / 3)

    Eq << Algebra.Gt_0.to.Eq.Arg.apply(Eq.p_is_positive, Mul(*Eq[-1].rhs.args[1:]))

    Eq << Algebra.Eq.to.Eq.Arg.apply(Eq[-2])

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.rhs.arg.apply(Algebra.Mul.eq.Exp)

    Eq.arg_p3_w = Eq[-1].this.lhs.find(Exp).apply(Geometry.ExpI.eq.Add.Euler)

    Eq << Sets.In.to.In.Sub.apply(Eq.p3_contains, S.Pi * 2, simplify=None)

    Eq << Sets.In.to.In.Div.Interval.apply(Eq[-1], 3, simplify=None)

    Eq << Sets.In.to.Eq.Arg.ExpI.apply(Eq[-1])

    Eq << Eq.arg_p3_w.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Arg[Mul]).apply(Algebra.Arg.Mul.eq.Add.st.Pow)

    Eq << Eq.eq_simplified.subs(Eq[-1])

    Eq << Eq[-1].this.find(ExprCondPair[Ceiling[Add[~Mul[Add]]]]).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.find(Add[~Ceiling]).apply(Algebra.Ceiling.eq.Add.half)





if __name__ == '__main__':
    run()
# created on 2018-11-08
# updated on 2022-01-23
