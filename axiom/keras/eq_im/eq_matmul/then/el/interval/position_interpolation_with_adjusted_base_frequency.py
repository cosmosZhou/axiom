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
    from axiom import discrete, algebra, sets, geometry

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

    Eq << Eq[1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs().find(Min[Mul]).simplify()

    Eq << Eq[-1].this.rhs().find(Min[Mul]).simplify()

    Eq << Eq[-1].this.rhs().find(Max).simplify()

    Eq << Eq[-1].this.rhs().find(Max).simplify()

    Eq << Eq[-1].this.rhs().find(Min).simplify()

    Eq << Eq[-1].this.rhs().find(Min).simplify()

    Eq.def_RoPE = Eq[-1].this.rhs.expr.apply(algebra.add.to.mul)

    Eq << Eq.def_RoPE.subs(t, t + 1)

    Eq << algebra.eq.then.eq.conj.apply(Eq[-1])

    Eq << Eq[-1] @ Eq.def_RoPE

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.sum)

    Eq << Eq[-1].this.rhs.expr.args[:2].apply(algebra.mul.to.add, deep=True)

    Eq << Eq[-1].this.find(Exp * Exp).args[-2:].apply(algebra.mul.to.exp)

    Eq << Eq[-1].this.find(Exp).arg.apply(algebra.add.to.mul)

    Eq << algebra.eq.then.eq.im.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.im.to.sum)

    Eq << Eq[-1].this.find(Pow * Pow).args[1:].apply(algebra.mul.to.pow.mul.base)

    Eq << algebra.eq.then.eq.norm.apply(Eq.def_RoPE)

    Eq << Eq[-1].this.rhs.apply(algebra.norm.to.sqrt)

    Eq << Eq[-1].subs(t, t + 1)

    Eq << Eq[0].subs(a_vec, f_RoPE(x, t + 1)).subs(b_vec, f_RoPE(x, t))

    Eq.eq_cos = Eq[-1].subs(Eq[-5], Eq[-3], Eq[-2])

    Eq << (Norm(x) ** 2).this.base.apply(algebra.norm.to.sqrt, simplify=None)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add.split, cond=Equal(Eq[-1].rhs.variable % 2, 0))

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.sum.halve)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.sum.halve)

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.sum)

    Eq.eq_cos = Eq.eq_cos.subs(Eq[-1].reversed)

    Eq.eq_cos = Eq.eq_cos * Norm(x) ** 2

    Eq << LessEqual(1 / (b * β), 1, plausible=True)

    Eq << GreaterEqual(1 / (b * β), 0, plausible=True)

    j = Symbol(domain=Range(d / 2))
    Eq << algebra.le.then.le.pow.apply(Eq[-2], 2 * j / d)

    Eq << LessEqual(α, 1, plausible=True)

    Eq << algebra.le.le.then.le.mul.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.find(Pow).apply(algebra.pow.to.mul.split.base)

    Eq << Eq[-1].this.find(Pow * Pow).args[1:].apply(algebra.mul.to.pow.mul.base)

    Eq.gt_zero_eta = Greater(α / (b * β) ** (2 * j / d), 0, plausible=True)

    Eq << sets.le.gt.then.el.interval.apply(Eq[-1], Eq.gt_zero_eta)

    Eq << geometry.el_interval.then.gt_zero.sin.apply(Eq[-1])

    Eq.gt_zero = algebra.cond.then.all.apply(Eq[-1], j)

    Eq << algebra.then.all.le.reducedMax.apply(ReducedMax(x ** 2))

    Eq << Eq[-1].subs(i, 2 * j) + Eq[-1].subs(i, 2 * j + 1)

    Eq << algebra.cond.then.all.apply(Eq[-1], j)

    Eq <<= Eq.gt_zero & Eq[-1]

    Eq << Eq[-1].this.expr.apply(algebra.gt_zero.le.then.le.mul)

    Eq.sum_le = algebra.all_le.then.le.sum.apply(Eq[-1])

    Eq << algebra.then.all.ge.reducedMin.apply(ReducedMin(x ** 2))

    Eq << Eq[-1].subs(i, 2 * j) + Eq[-1].subs(i, 2 * j + 1)

    Eq << algebra.cond.then.all.apply(Eq[-1], j)

    Eq <<= Eq.gt_zero & Eq[-1]

    Eq << Eq[-1].this.expr.apply(algebra.gt_zero.ge.then.ge.mul)

    Eq.sum_ge = algebra.all_ge.then.ge.sum.apply(Eq[-1])

    Eq << geometry.then.sin_ge.quadratic.apply(Eq.gt_zero_eta.lhs)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add)

    Eq << algebra.cond.then.all.apply(Eq[-1], j)

    Eq << algebra.all_ge.then.ge.sum.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.mul.series.geometric)

    Eq.sum_ge_piece = Eq[-1].this.find(Piecewise).apply(algebra.piece.swap)

    # Eq << Less(1 / (b * β) ** (2 / d), 1, plausible=True)
    Eq << Less(1 / (b * β), 1, plausible=True)

    Eq << algebra.lt.then.lt.pow.apply(Eq[-1], 2 / d, evaluate=False)

    Eq << Eq[-1].this.lhs.apply(algebra.pow.to.mul.split.base)

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.pow.mul.base)

    Eq.gt_zero_2_bβ = algebra.lt.then.gt_zero.apply(Eq[-1])

    Eq.ne = algebra.lt.then.ne.apply(Eq[-1])

    Eq << algebra.lt.then.lt.pow.apply(Eq[-1], 2, evaluate=False)

    Eq.ne4 = algebra.lt.then.ne.apply(Eq[-1])

    Eq << algebra.cond.cond.then.cond.subs.apply(Eq.ne, Eq.sum_ge_piece)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.mul.series.geometric)

    Eq << Eq[-1].this.find(Piecewise).apply(algebra.piece.swap)

    Eq << algebra.cond.cond.then.cond.subs.apply(Eq.ne4, Eq[-1])

    Eq << Eq[-1].this.find(1 - Expr ** -2 * Expr ** -2).apply(algebra.sub.square.to.mul)

    Eq << Eq[-1].this.rhs.args[1].find(1 - Mul ** Mul).apply(algebra.sub.square.to.mul)

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.mul)

    Eq << Eq[-1] * (2 * ReducedMin(x ** 2))

    Eq.sum_ge = algebra.ge.ge.then.ge.trans.apply(Eq.sum_ge, Eq[-1])

    Eq << geometry.gt_zero.then.sin_le.apply(Eq.gt_zero_eta)

    Eq << algebra.cond.then.all.apply(Eq[-1], j)

    Eq << algebra.all_le.then.le.sum.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.mul.series.geometric)

    Eq << Eq[-1].this.find(Piecewise).apply(algebra.piece.swap)

    Eq << algebra.cond.cond.then.cond.subs.apply(Eq.ne, Eq[-1])

    Eq << Eq[-1] * (2 * ReducedMax(x ** 2))

    Eq.sum_le = algebra.le.le.then.le.trans.apply(Eq.sum_le, Eq[-1])

    Eq << sets.ge.le.then.el.interval.apply(Eq.sum_ge, Eq.sum_le)

    Eq << Eq[-1].subs(Eq.eq_cos.reversed)

    Eq << Greater(2 * α * (1 - 1 / (b * β)), 0, plausible=True)

    Eq << algebra.gt_zero.gt_zero.then.gt_zero.div.apply(Eq[-1], Eq.gt_zero_2_bβ)

    Eq << sets.gt_zero.el.then.el.div.apply(Eq[-1], Eq[-3])

    # reference:
    # https://arxiv.org/pdf/2309.16039.pdf#page=18




if __name__ == '__main__':
    run()
# created on 2023-10-02
# updated on 2023-10-04
