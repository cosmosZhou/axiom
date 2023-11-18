from util import *


@apply
def apply(eq_z, eq):
    p, z = eq_z.of(Equal[Expr @ Matrix[One, ImaginaryUnit]])
    assert p.shape == (3, 2)
    (S[z[2]], S[z[0]]), ((S[z[1]], S[z[0]]), theta) = eq.of(Equal[Expr - Expr, (Expr - Expr) * Exp[Mul[ImaginaryUnit]]])
    return Equal(p[2] - p[0], Matrix(((cos(theta), -sin(theta)), (sin(theta), cos(theta)))) @ (p[1] - p[0]))


@prove
def prove(Eq):
    from axiom import geometry, algebra, discrete

    p = Symbol(real=True, shape=(3, 2))
    theta = Symbol(real=True)
    z = Symbol(complex=True, shape=(3,))
    Eq << apply(Equal(z, p @ Matrix((1, S.ImaginaryUnit))),
                Equal(z[2] - z[0], (z[1] - z[0]) * exp(S.ImaginaryUnit * theta)))

    Eq << Eq[1].this.find(Exp).apply(geometry.expi.to.add.Euler)

    Eq.p_def = algebra.expr.to.matrix.apply(p)

    Eq << Eq[0].subs(Eq.p_def)

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.matrix)

    Eq <<= Eq[-1][0], Eq[-1][1], Eq[-1][2]

    Eq << Eq[3].subs(Eq[-1], Eq[-2], Eq[-3])

    Eq << Eq[-1].this.rhs.expand()

    Eq.real_part = algebra.eq.imply.eq.re.apply(Eq[-1])

    Eq.imaginary_part = algebra.eq.imply.eq.im.apply(Eq[-1])

    Eq <<= Eq.p_def[0], Eq.p_def[1], Eq.p_def[2]

    Eq << Eq[2].subs(Eq[-1], Eq[-3], Eq[-2])

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.matrix)

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1].subs(Eq.real_part.reversed, Eq.imaginary_part.reversed)

    Eq << Eq[-1] + Eq[-1].find(-~Matrix)




if __name__ == '__main__':
    run()
# created on 2022-07-02
