from util import *


@apply
def apply(eq_cosine_similarity, eq_rotary_ABF):
    (((t, α, ((base, β), (j, d))), (S[j], S[0], S[d / 2])), x), f_RoPE = eq_rotary_ABF.of(Equal[Lamda[BlockMatrix[ZeroMatrix, Exp[Symbol * Symbol * -S.ImaginaryUnit * (Symbol * Symbol) ** (-2 * Symbol / Symbol)] * Matrix[One, S.ImaginaryUnit], ZeroMatrix]] @ Expr])

    assert 0 < α <= 1
    assert β >= 1 and base >= 1

    ((a, b), S[a], S[b]), cosine_f = eq_cosine_similarity.of(Equal[Im[Conjugate[Symbol] @ Symbol] / Norm / Norm])

    return Element(
        cosine_f._subs(a, f_RoPE._subs(t, t + 1))._subs(b, f_RoPE) * Norm(x) ** 2 * (1 - (base * β) ** (-2 / d)) / (2*α*(1 - 1 / (base*β))),
        Interval(
            ReducedMin(x ** 2) * (-α * (1 + 1 / (base * β)) / (S.Pi * (1 + (base * β) ** (-2 / d))) + 1),
            ReducedMax(x ** 2)))

@prove
def prove(Eq):
    from Axiom import Discrete, Algebra, Sets, Geometry

    # N denotes sequence length (seq_length)
    # b denotes 10000 adjusted to 500000
    N, b = Symbol(integer=True, positive=True)
    # d denotes embedding size which must be even
    d = Symbol(integer=True, positive=True, even=True)
    # x denotes token embedding at index k (ie, x denotes sentence embedding)
    x = Symbol(shape=(d,), real=True)
    # R denotes rotary matrix function
    R = Function(shape=(d, d), real=True)
    θ = Symbol(shape=(N, d / 2), real=True)
    # k denotes token index
    # i denotes row index
    i, k, j, t = Symbol(integer=True)
    # α, β denotes scaling factor
    α = Symbol(domain=Interval.Lopen(0, 1))
    β = Symbol(domain=Interval.Lopen(1, oo))
    f_RoPE = Function('f^{RoPE}', complex=True, shape=(d / 2,))
    cos_similarity = Function("cos∠", real=True, shape=())
    a_vec = Symbol(r"\vec{a}", complex=True, shape=(d / 2,))
    b_vec = Symbol(r"\vec{b}", complex=True, shape=(d / 2,))
    Eq << apply(
        Equal(
            cos_similarity(a_vec, b_vec),
            Im(~a_vec @ b_vec, evaluate=False) / (Norm(a_vec) * Norm(b_vec))),
        Equal(
            f_RoPE(x, t),
            Lamda[j:d / 2]([ZeroMatrix(j * 2), exp(-S.ImaginaryUnit * t * α / (β * b) ** (2 * j / d)) * [1, S.ImaginaryUnit], ZeroMatrix(d - 2 - j * 2)]) @ x))

    Eq << Eq[1].this.rhs.apply(Discrete.Dot.eq.Lamda)

    Eq << Eq[-1].this.rhs().find(Min[Mul]).simplify()

    Eq << Eq[-1].this.rhs().find(Min[Mul]).simplify()

    Eq << Eq[-1].this.rhs().find(Max).simplify()

    Eq << Eq[-1].this.rhs().find(Max).simplify()

    Eq << Eq[-1].this.rhs().find(Min).simplify()

    Eq << Eq[-1].this.rhs().find(Min).simplify()

    Eq.def_RoPE = Eq[-1].this.rhs.expr.apply(Algebra.Add.eq.Mul)

    Eq << Eq.def_RoPE.subs(t, t + 1)

    Eq << Algebra.Eq.to.Eq.Conj.apply(Eq[-1])

    Eq << Eq[-1] @ Eq.def_RoPE

    Eq << Eq[-1].this.rhs.apply(Discrete.Dot.eq.Sum)

    Eq << Eq[-1].this.rhs.expr.args[:2].apply(Algebra.Mul.eq.Add, deep=True)

    Eq << Eq[-1].this.find(Exp * Exp).args[-2:].apply(Algebra.Mul.eq.Exp)

    Eq << Eq[-1].this.find(Exp).arg.apply(Algebra.Add.eq.Mul)

    Eq << Algebra.Eq.to.Eq.Im.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Im.eq.Sum)

    Eq << Eq[-1].this.find(Pow * Pow).args[1:].apply(Algebra.Mul.eq.Pow.Mul.base)

    Eq << Algebra.Eq.to.Eq.Norm.apply(Eq.def_RoPE)

    Eq << Eq[-1].this.rhs.apply(Algebra.Norm.eq.Sqrt)

    Eq << Eq[-1].subs(t, t + 1)

    Eq << Eq[0].subs(a_vec, f_RoPE(x, t + 1)).subs(b_vec, f_RoPE(x, t))

    Eq.eq_cos = Eq[-1].subs(Eq[-5], Eq[-3], Eq[-2])

    Eq << (Norm(x) ** 2).this.base.apply(Algebra.Norm.eq.Sqrt, simplify=None)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Add.split, cond=Equal(Eq[-1].rhs.variable % 2, 0))

    Eq << Eq[-1].this.rhs.args[0].apply(Algebra.Sum.halve)

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Sum.halve)

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Sum)

    Eq.eq_cos = Eq.eq_cos.subs(Eq[-1].reversed)

    Eq.eq_cos = Eq.eq_cos * Norm(x) ** 2

    Eq << LessEqual(1 / (b * β), 1, plausible=True)

    Eq << GreaterEqual(1 / (b * β), 0, plausible=True)

    j = Symbol(domain=Range(d / 2))
    Eq << Algebra.Le.to.Le.Pow.apply(Eq[-2], 2 * j / d)

    Eq << LessEqual(α, 1, plausible=True)

    Eq << Algebra.Le.Le.to.Le.Mul.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.find(Pow).apply(Algebra.Pow.eq.Mul.split.base)

    Eq << Eq[-1].this.find(Pow * Pow).args[1:].apply(Algebra.Mul.eq.Pow.Mul.base)

    Eq.gt_zero_eta = Greater(α / (b * β) ** (2 * j / d), 0, plausible=True)

    Eq << Sets.Le.Gt.to.In.Interval.apply(Eq[-1], Eq.gt_zero_eta)

    Eq << Geometry.In_Interval.to.Gt_0.Sin.apply(Eq[-1])

    Eq.gt_zero = Algebra.Cond.to.All.apply(Eq[-1], j)

    Eq << Algebra.All_Le_ReducedMax.apply(ReducedMax(x ** 2))

    Eq << Eq[-1].subs(i, 2 * j) + Eq[-1].subs(i, 2 * j + 1)

    Eq << Algebra.Cond.to.All.apply(Eq[-1], j)

    Eq <<= Eq.gt_zero & Eq[-1]

    Eq << Eq[-1].this.expr.apply(Algebra.Gt_0.Le.to.Le.Mul)

    Eq.Sum_le = Algebra.All_Le.to.Le.Sum.apply(Eq[-1])

    Eq << Algebra.All_Ge_ReducedMin.apply(ReducedMin(x ** 2))

    Eq << Eq[-1].subs(i, 2 * j) + Eq[-1].subs(i, 2 * j + 1)

    Eq << Algebra.Cond.to.All.apply(Eq[-1], j)

    Eq <<= Eq.gt_zero & Eq[-1]

    Eq << Eq[-1].this.expr.apply(Algebra.Gt_0.Ge.to.Ge.Mul)

    Eq.Sum_ge = Algebra.All_Ge.to.Ge.Sum.apply(Eq[-1])

    Eq << Geometry.Sin.ge.Mul_Sub_.One.Div_Pi.quadratic.apply(Eq.gt_zero_eta.lhs)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.eq.Add)

    Eq << Algebra.Cond.to.All.apply(Eq[-1], j)

    Eq << Algebra.All_Ge.to.Ge.Sum.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Add)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.eq.Mul.series.geometric)

    Eq.Sum_ge_piece = Eq[-1].this.find(Piecewise).apply(Algebra.Piece.swap)

    # Eq << Less(1 / (b * β) ** (2 / d), 1, plausible=True)
    Eq << Less(1 / (b * β), 1, plausible=True)

    Eq << Algebra.Lt.to.Lt.Pow.apply(Eq[-1], 2 / d, evaluate=False)

    Eq << Eq[-1].this.lhs.apply(Algebra.Pow.eq.Mul.split.base)

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul.eq.Pow.Mul.base)

    Eq.gt_zero_2_bβ = Algebra.Lt.to.Gt_0.apply(Eq[-1])

    Eq.ne = Algebra.Lt.to.Ne.apply(Eq[-1])

    Eq << Algebra.Lt.to.Lt.Pow.apply(Eq[-1], 2, evaluate=False)

    Eq.ne4 = Algebra.Lt.to.Ne.apply(Eq[-1])

    Eq << Algebra.Cond.Cond.to.Cond.subs.apply(Eq.ne, Eq.Sum_ge_piece)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.eq.Mul.series.geometric)

    Eq << Eq[-1].this.find(Piecewise).apply(Algebra.Piece.swap)

    Eq << Algebra.Cond.Cond.to.Cond.subs.apply(Eq.ne4, Eq[-1])

    Eq << Eq[-1].this.find(1 - Expr ** -2 * Expr ** -2).apply(Algebra.Sub.Square.eq.Mul)

    Eq << Eq[-1].this.rhs.args[1].find(1 - Mul ** Mul).apply(Algebra.Sub.Square.eq.Mul)

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Mul)

    Eq << Eq[-1] * (2 * ReducedMin(x ** 2))

    Eq.Sum_ge = Algebra.Ge.Ge.to.Ge.trans.apply(Eq.Sum_ge, Eq[-1])

    Eq << Geometry.Gt_0.to.LeSin.apply(Eq.gt_zero_eta)

    Eq << Algebra.Cond.to.All.apply(Eq[-1], j)

    Eq << Algebra.All_Le.to.Le.Sum.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.eq.Mul.series.geometric)

    Eq << Eq[-1].this.find(Piecewise).apply(Algebra.Piece.swap)

    Eq << Algebra.Cond.Cond.to.Cond.subs.apply(Eq.ne, Eq[-1])

    Eq << Eq[-1] * (2 * ReducedMax(x ** 2))

    Eq.Sum_le = Algebra.Le.Le.to.Le.trans.apply(Eq.Sum_le, Eq[-1])

    Eq << Sets.Ge.Le.to.In.Interval.apply(Eq.Sum_ge, Eq.Sum_le)

    Eq << Eq[-1].subs(Eq.eq_cos.reversed)

    Eq << Greater(2 * α * (1 - 1 / (b * β)), 0, plausible=True)

    Eq << Algebra.Gt_0.Gt_0.to.Gt_0.Div.apply(Eq[-1], Eq.gt_zero_2_bβ)

    Eq << Sets.Gt_0.In.to.In.Div.apply(Eq[-1], Eq[-3])

    # reference:
    # https://arxiv.org/pdf/2309.16039.pdf#page=18




if __name__ == '__main__':
    run()
# created on 2023-10-02
# updated on 2023-10-04
