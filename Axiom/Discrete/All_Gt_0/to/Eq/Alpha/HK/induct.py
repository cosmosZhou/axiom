from util import *


@apply
def apply(given):
    from Axiom.Discrete.Alpha.gt.Zero import alpha
    from Axiom.Discrete.H.eq.Add.definition import H
    from Axiom.Discrete.K.eq.Add.definition import K
    (x, j), (S[j], n) = given.of(All[Indexed > 0, Tuple[1, Expr]])
    assert n >= 3
    assert x.is_real
    return Equal(alpha(x[:n]), H(x[:n]) / K(x[:n]))


@prove
def prove(Eq):
    from Axiom import Algebra, Discrete
    from Axiom.Discrete.Alpha.gt.Zero import alpha
    from Axiom.Discrete.H.eq.Add.definition import H
    from Axiom.Discrete.K.eq.Add.definition import K

    x = Symbol(real=True, shape=(oo,))
    n = Symbol(integer=True, positive=True)
    j = Symbol(integer=True)
    n = Symbol(domain=Range(2, oo), given=False)
    Eq << apply(All[j:1:n + 1](x[j] > 0))

    Eq.hypothesis = Imply(Eq[0], Eq[1], plausible=True)

    Eq.initial = Eq.hypothesis.subs(n, 2)

    Eq << Eq.initial.this.lhs.doit()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(H).defun()

    Eq << Eq[-1].this.find(H).defun()

    Eq << Eq[-1].this.find(H).defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.lhs.apply(Algebra.Gt_0.Gt_0.to.Gt_0)

    Eq << Eq[-1].this.lhs + 1

    Eq << Eq[-1].this.lhs.apply(Algebra.Gt.to.Ne_0)

    Eq << Algebra.Imply.of.Imply.And.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Ne_0.Eq.of.And.Mul)

    Eq << Eq[-1].this.rhs.lhs.ratsimp()

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq.alpha_recurrence = Eq.induct.lhs.this.apply(Discrete.All_Gt_0.to.Eq.Alpha.recurrence)

    # try to avoid using reciprocal expression, instead, using find(1 / Expr) to ensure logical correctness!
    Eq << Algebra.Cond.to.Cond.subs.apply(Eq.hypothesis, x[:n + 1], BlockMatrix(x[:n], Eq.alpha_recurrence.find(Indexed + 1 / Indexed)))

    Eq << Eq[-1].this.rhs.lhs.apply(Discrete.Alpha.Block)

    Eq << Eq[-1].this.lhs.apply(Algebra.All.of.And.All, cond={n})

    Eq << Eq[-1].this.find(All)().expr.simplify()

    Eq << Eq[-1].this.find(Greater).apply(Algebra.Gt_.Add.Zero.of.And.Gt_0)

    Eq << Eq[-1].this.find(Greater[2]).apply(Algebra.Gt_0.of.Gt_0.Inv)

    Eq << Eq[-1].this.lhs.apply(Algebra.And.equ.All.limits.push)

    Eq <<= Eq.alpha_recurrence & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Eq.to.Eq.trans, reverse=True)

    Eq << Eq[-1].this.find(H).defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.rhs.rhs.ratsimp()

    Eq << Eq.induct.this.find(H).defun()

    Eq << Eq[-1].this.find(Indexed * ~H).defun()

    Eq << Eq[-1].this.find(Mul, Add).expand()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.find(Indexed * ~K).defun()

    Eq << Eq[-1].this.find(Pow, Add).expand()

    Eq << Imply(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << Algebra.Cond.Imply.to.Cond.induct.apply(Eq.initial, Eq[-1], n, 2)

    Eq << Algebra.Cond.Imply.to.Cond.trans.apply(Eq[0], Eq.hypothesis)





if __name__ == '__main__':
    run()
# created on 2020-05-21
# updated on 2023-06-24