from util import *


from axiom.discrete.H.to.add.definition import H
from axiom.discrete.K.to.add.definition import K
from axiom.discrete.imply.gt_zero.alpha import alpha


@apply
def apply(given):
    (x, j), (S[j], n) = given.of(All[Indexed > 0, Tuple[1, Expr]])
    assert n >= 3
    assert x.is_real
    return Equal(alpha(x[:n]), H(x[:n]) / K(x[:n]))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    x = Symbol(real=True, shape=(oo,))
    n = Symbol(integer=True, positive=True)
    j = Symbol(integer=True)
    n = Symbol(domain=Range(2, oo), given=False)
    Eq << apply(All[j:1:n + 1](x[j] > 0))

    Eq.hypothesis = Infer(Eq[0], Eq[1], plausible=True)

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

    Eq << Eq[-1].this.lhs.apply(algebra.gt_zero.gt_zero.imply.gt_zero)

    Eq << Eq[-1].this.lhs + 1

    Eq << Eq[-1].this.lhs.apply(algebra.gt.imply.ne_zero)

    Eq << algebra.infer.given.infer.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.ne_zero.eq.given.et.mul)

    Eq << Eq[-1].this.rhs.lhs.ratsimp()

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq.alpha_recurrence = Eq.induct.lhs.this.apply(discrete.all_gt_zero.imply.eq.alpha.recurrence)

    # try to avoid using reciprocal expression, instead, using find(1 / Expr) to ensure logical correctness!
    Eq << algebra.cond.imply.cond.subs.apply(Eq.hypothesis, x[:n + 1], BlockMatrix(x[:n], Eq.alpha_recurrence.find(Indexed + 1 / Indexed)))

    Eq << Eq[-1].this.rhs.lhs.apply(discrete.alpha.block)

    Eq << Eq[-1].this.lhs.apply(algebra.all.given.et.all, cond={n})

    Eq << Eq[-1].this.find(All)().expr.simplify()

    Eq << Eq[-1].this.find(Greater).apply(algebra.add_gt_zero.given.et.gt_zero)

    Eq << Eq[-1].this.find(Greater[2]).apply(algebra.gt_zero.given.gt_zero.inverse)

    Eq << Eq[-1].this.lhs.apply(algebra.et.to.all.limits.push)

    Eq <<= Eq.alpha_recurrence & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(algebra.eq.eq.imply.eq.transit, reverse=True)

    Eq << Eq[-1].this.find(H).defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.rhs.rhs.ratsimp()

    Eq << Eq.induct.this.find(H).defun()

    Eq << Eq[-1].this.find(Indexed * ~H).defun()

    Eq << Eq[-1].this.find(Mul, Add).expand()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.find(Indexed * ~K).defun()

    Eq << Eq[-1].this.find(Pow, Add).expand()

    Eq << Infer(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << algebra.cond.infer.imply.cond.induct.apply(Eq.initial, Eq[-1], n, 2)

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq.hypothesis)





if __name__ == '__main__':
    run()
# created on 2020-05-21
# updated on 2023-06-24
