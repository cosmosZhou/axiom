from util import *


@apply
def apply(is_zero, eq, x=None):
    from axiom.algebra.poly_is_zero.imply.et.infer.cubic import cubic_coefficient
    fx = is_zero.of(Equal[0])
    S[1], S[0], p, q = cubic_coefficient(fx, x=x)

    (((arg_p, coeff), half), ((arg_AB, S[coeff]), S[half])), d = eq.of(Equal[Ceiling[Arg * Expr - Expr] - Ceiling[Arg * Expr - Expr]])
    assert coeff == 3 / (S.Pi * 2)
    assert half == S.One / 2

    delta = 4 * p ** 3 / 27 + q ** 2

    A = (sqrt(delta) / 2 - q / 2) ** (S.One / 3)
    B = (-sqrt(delta) / 2 - q / 2) ** (S.One / 3)

    assert Arg(A * B).arg == arg_AB
    assert Arg(-p).arg == arg_p

    w = -S.One / 2 + S.ImaginaryUnit * sqrt(3) / 2
    d %= 3

    if d == 0:
        return Equal(x, A + B) | Equal(x, A * w + B * ~w) | Equal(x, A * ~w + B * w)
    elif d == 1:
        return Equal(x, A * w + B) | Equal(x, A * ~w + B * ~w) | Equal(x, A + B * w)
    else:
        return Equal(x, A * ~w + B) | Equal(x, A + B * ~w) | Equal(x, A * w + B * w)


@prove
def prove(Eq):
    from axiom import algebra

    x, p = Symbol(complex=True, given=True)
    q = Symbol(real=True, given=True)
    delta = 4 * p ** 3 / 27 + q ** 2
    A = (sqrt(delta) / 2 - q / 2) ** (S.One / 3)
    B = (-sqrt(delta) / 2 - q / 2) ** (S.One / 3)
    Eq << apply(Equal(x ** 3 + p * x + q, 0),
                Equal(Ceiling(3 * Arg(-p / 3) / (S.Pi * 2) - S.One / 2) - Ceiling(3 * Arg(A * B) / (S.Pi * 2) - S.One / 2), 1),
                x=x)

    B = Symbol(Eq[2].args[0].rhs.args[0].args[1])
    Eq.B_def = B.this.definition

    A = Symbol(Eq[2].args[0].rhs.args[1])
    Eq.A_def = A.this.definition

    Eq.w, Eq.w_conj, Eq.add_ww, Eq.mul_ww, Eq.w_square, Eq.w_conj_square, Eq.w3 = algebra.imply.et.eq.omega.apply('omega')

    w = Eq.w.lhs
    Eq.w_sub = Eq.add_ww.this.apply(algebra.eq.transport)

    Eq.w3_conj = algebra.eq.imply.eq.conjugate.apply(Eq.w3)

    A_ = A * w
    Eq << ((x - A_ * ~w - B * w) * (x - A_ * w - B * ~w) * (x - A_ - B)).this.apply(algebra.mul.to.add.poly, x)

    Eq << Eq[-1].subs(Eq.w_square)

    Eq.expand = Eq[-1].subs(Eq.mul_ww)

    Eq << Eq.expand.find(Symbol * ~Add).this.args[0].apply(algebra.mul.to.add, deep=True)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(algebra.mul.to.add, deep=True, simplify=None)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(algebra.mul.to.add, deep=True)

    Eq << Eq[-1].subs(Eq.w_square, Eq.mul_ww)

    Eq << Eq[-1].this.rhs.apply(algebra.add.collect, factor=A ** 2)

    Eq << Eq[-1].this.rhs.apply(algebra.add.collect, factor=B ** 2)

    Eq << Eq[-1].subs(Eq.add_ww)

    Eq << Eq[-1].this.rhs.subs(Eq.w_sub)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(algebra.mul.to.add, deep=True)

    Eq.expand = Eq.expand.subs(Eq[-1])

    Eq << Eq.expand.find(Symbol ** 2 * ~Add).this.apply(algebra.add.collect, factor=A)

    Eq << Eq[-1].this.rhs.apply(algebra.add.collect, factor=B)

    Eq << Eq[-1].subs(Eq.add_ww)

    Eq.expand = Eq.expand.subs(Eq[-1])

    Eq << -Eq.expand.rhs.args[1].this.apply(algebra.mul.to.add, deep=True)

    Eq << Eq[-1].subs(Eq.mul_ww, Eq.w_square)

    Eq << Eq[-1].this.rhs.apply(algebra.add.collect, factor=A ** 2 * B)

    Eq << Eq[-1].this.rhs.apply(algebra.add.collect, factor=B ** 2 * A)

    Eq << Eq[-1].subs(Eq.add_ww)

    Eq.expand = Eq.expand.subs(Eq[-1])

    Eq.A3_def = algebra.eq.imply.eq.pow.apply(Eq.A_def, exp=3)

    Eq.B3_def = algebra.eq.imply.eq.pow.apply(Eq.B_def, exp=3)

    Eq << Eq.A3_def + Eq.B3_def

    Eq.expand = Eq.expand.subs(Eq[-1])

    Eq << Eq.A_def * Eq.B_def

    Eq << Eq[-1] ** 3

    Eq.eq_pow = Eq[-1].this.rhs.apply(algebra.mul.to.add, deep=True)

    Eq <<= Eq.A_def * 2 ** (S.One / 3), Eq.B_def * 2 ** (S.One / 3)

    Eq <<= Eq[-2].this.rhs.apply(algebra.mul.to.pow.mul.base), Eq[-1].this.rhs.apply(algebra.mul.to.pow.mul.base)

    Eq << Eq[1].subs(Eq[-2].reversed, Eq[-1].reversed)

    Eq << algebra.eq_pow.imply.eq.cubic_root.omega.apply(Eq.eq_pow)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1] * w

    Eq << Eq[-1].this.rhs.subs(Eq.w)

    Eq << Eq[-1].this.find(Exp).apply(algebra.expr.to.add.complex)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add, deep=True)

    Eq << Eq.expand.subs(Eq[-1])

    Eq << Eq[-1].subs(Eq[0])

    Eq << algebra.mul_is_zero.imply.ou.is_zero.apply(Eq[-1])

    Eq << Eq[-1].this.args[0].reversed

    Eq << Eq[-1].this.args[0].reversed

    Eq << Eq[-1].this.args[0].reversed

    Eq << Eq[-1].subs(Eq.A_def, Eq.B_def, Eq.w, Eq.w_conj)





if __name__ == '__main__':
    run()
# created on 2018-11-15
# updated on 2022-01-15
