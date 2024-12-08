from util import *


@apply
def apply(m_is_nonnegative, lt_mM, lt, x=None):
    m = m_is_nonnegative.of(Expr >= 0)
    S[m], M = lt_mM.of(Less)

    U, M2 = lt.of(Less)
    _M = M2.of(Expr ** 2)
    assert _M == M or _M == -M
    if x is None:
        x = lt.generate_var(real=True)
    return Any[x:Interval(m, M, left_open=True, right_open=True)](x ** 2 > U)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    m, M, U = Symbol(real=True, given=True)
    Eq << apply(m >= 0, m < M, U < M ** 2)

    x = Eq[-1].variable
    Eq.ge, Eq.lt = Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=U >= m ** 2)

    Eq << Algebra.Lt.Ge.to.Gt.trans.apply(Eq[1], Eq[0])

    Eq << Eq.lt.this.rhs.apply(Algebra.Any.of.Cond.subs, x, (m + M) / 2)

    Eq.gt, Eq.contains = Algebra.Imply.of.And.Imply.apply(Eq[-1])

    Eq << Eq[1].reversed + m

    Eq << Eq[-1] / 2

    Eq << Algebra.Ge_0.Gt.to.Gt.Square.apply(Eq[0], Eq[-1])

    Eq << Algebra.Cond.to.Imply.And.apply(Eq[-1], cond=U < m ** 2)

    Eq << Eq[-1].this.rhs.apply(Algebra.Gt.Lt.to.Gt.trans)

    Eq << Algebra.Imply.of.Cond.apply(Eq.contains)

    Eq << Sets.Lt.to.In.Interval.average.apply(Eq[1])

    Eq << Eq.ge.this.rhs.apply(Algebra.Any.of.Cond.subs, x, (sqrt(U) + M) / 2)

    Eq << Eq[-1].this.find(Element).apply(Sets.In_Interval.of.And)

    Eq << Algebra.Imply.of.And.Imply.apply(Eq[-1], index=None)

    Eq <<= Eq[-1].this.rhs.apply(Algebra.Gt.of.Gt_0), Eq[-3].this.rhs.apply(Algebra.Lt.transport, lhs=0)

    Eq <<= Eq[-2].this.find(Add).apply(Algebra.Sub.Square.eq.Mul), Eq[-1].this.rhs * 2

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Ge.to.Ge.relax, lower=0), Eq[-1].this.lhs.apply(Algebra.Ge.to.Ge.relax, lower=0)

    Eq.is_nonnegative = Eq[-2].this.rhs.apply(Algebra.Gt_.Mul.Zero.of.And.Gt_0)

    Eq <<= Algebra.Cond.to.Imply.And.apply(Eq[2], cond=U >= 0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ge_0.Lt.to.Lt.Sqrt)

    Eq << Algebra.Gt_0.to.Eq.Abs.apply(Eq[4])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Algebra.Imply.of.And.Imply.apply(Eq.is_nonnegative)

    Eq <<= Eq[-2].this.rhs * 2, Eq[-1].this.rhs * 2

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Gt_.Add.Zero.of.And, 0), Eq[-1].this.rhs.apply(Algebra.Gt_0.of.Gt)

    Eq <<= Eq[-2].this.rhs.args[1] / 3, Eq[-1].this.rhs.reversed

    Eq <<= Algebra.Imply.of.And.Imply.apply(Eq[-1])

    Eq <<= Algebra.Imply.of.Cond.apply(Eq[-2])

    Eq <<= Eq[-1].this.lhs.apply(Algebra.Ge_0.to.Ge_0.Sqrt)

    Eq << Algebra.Cond.to.Imply.And.apply(Eq[1].reversed, cond=U >= m ** 2)

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Ge.to.Ge.Sqrt)

    Eq << Algebra.Ge_0.to.Eq.Abs.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Gt.Ge.to.Gt.Add)

    Eq << Eq[-1].this.rhs / 2





if __name__ == '__main__':
    run()
# created on 2019-07-07
# updated on 2023-05-20
