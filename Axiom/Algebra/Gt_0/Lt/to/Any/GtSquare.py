from util import *


@apply
def apply(M_is_positive, lt, x=None):
    M = M_is_positive.of(Expr > 0)
    U, m2 = lt.of(Less)
    S[M] = m2.of(Expr ** 2)

    if x is None:
        x = lt.generate_var(real=True)
    return Any[x:Interval(-M, M, left_open=True, right_open=True)](x ** 2 > U)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    M, U = Symbol(real=True, given=True)
    Eq << apply(M > 0, U < M ** 2)

    x = Eq[-1].variable
    Eq.is_negative, Eq.is_nonnegative = Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=U < 0)

    Eq << Algebra.Cond.to.Imply.apply(Eq[0], cond=U >= 0)

    Eq << Algebra.Cond.to.Imply.And.apply(Eq[1], cond=Eq[-1].lhs)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ge_0.Lt.to.Lt.Sqrt)

    Eq << Algebra.Gt_0.to.Eq.Abs.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq.is_negative.this.rhs.apply(Algebra.Any.of.Cond.subs, x, 0)

    Eq << Algebra.Imply.of.And.Imply.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Sets.In_Interval.of.And)

    Eq << Algebra.Imply.of.Cond.apply(Eq[-1])

    Eq << Eq[0].reversed

    Eq << Eq.is_nonnegative.this.rhs.apply(Algebra.Any.of.Cond.subs, x, (sqrt(U) + M) / 2)

    Eq << Algebra.Imply.of.And.Imply.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Gt.of.Gt_0), Eq[-1].this.rhs.apply(Sets.In_Interval.of.And)

    Eq <<= Eq[-2].this.find(Add).apply(Algebra.Sub.Square.eq.Mul), Algebra.Imply.of.And.Imply.apply(Eq[-1])

    Eq <<= Eq[-3].this.rhs.apply(Algebra.Gt_.Mul.Zero.of.And.Gt_0), Eq[-2].this.rhs * 2, Eq[-1].this.rhs * 2

    Eq <<= Algebra.Imply.of.And.Imply.apply(Eq[-3]), Eq[-2].this.rhs.apply(Algebra.Lt.transport, lhs=0), Eq[-1].this.rhs.apply(Algebra.Gt.of.Gt_0)

    Eq <<= Eq[-3].this.rhs * 2, Eq[-2].this.rhs * 2, Eq[-1].this.rhs.apply(Algebra.Gt_.Add.Zero.of.And, index=1)

    Eq <<= Eq[-3].this.rhs.apply(Algebra.Gt_.Add.Zero.of.And, index=0), Eq[-2].this.rhs.apply(Algebra.Gt.transport), Algebra.Imply.of.And.Imply.apply(Eq[-1])

    Eq <<= Algebra.Imply.of.And.Imply.apply(Eq[-4]), Eq[-3].this.rhs.reversed, Eq[-2].this.rhs / 3, Eq[-1].this.lhs.apply(Algebra.Ge_0.to.Ge_0.Sqrt)

    Eq << Eq[-1].this.rhs / 3





if __name__ == '__main__':
    run()
# created on 2019-08-26
# updated on 2023-05-20
