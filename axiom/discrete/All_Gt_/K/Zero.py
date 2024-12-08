from util import *


@apply
def apply(x, n):
    from Axiom.Discrete.K.eq.Add.definition import K
    return All[x[:n]:CartesianSpace(Range(1, oo), n)](Greater(K(x[:n]), 0))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x = Symbol(integer=True, shape=(oo,))
    n = Symbol(integer=True, positive=True, given=False)
    Eq << apply(x, n)

    Eq.initial0 = Eq[-1].subs(n, 1)

    Eq << Eq.initial0.this.expr.lhs.defun()

    Eq.initial1 = Eq[-1].subs(n, 2)

    Eq << Eq.initial1.this.expr.lhs.defun()

    Eq << Algebra.All.of.All.limits.split.apply(Eq[-1], index=1)

    Eq << Algebra.All.of.Or.apply(Eq[-1])

    Eq.induct = Eq[0].subs(n, n + 2)

    Eq << Eq.induct.this.expr.lhs.defun()

    Eq << Eq[0].this.expr.apply(Algebra.Cond.to.All.restrict, (x[n:n + 2], CartesianSpace(Range(1, oo), 2)), simplify=None)

    Eq.is_positive = Algebra.All.to.All.limits.merge.apply(Eq[-1])

    Eq.hypothesis = Eq[0].subs(n, n + 1)

    Eq << Eq.hypothesis.this.expr.apply(Algebra.Cond.to.All.restrict, (x[n + 1], 1, oo), simplify=None)

    Eq << Algebra.All.to.All.And.apply(Eq[-1], index=0)

    Eq << Algebra.All.to.All.limits.merge.apply(Eq[-1])

    Eq << Eq[-1].this.expr.args[1].apply(Sets.In_Range.to.Ge)

    Eq << Eq[-1].this.expr.args[1].apply(Algebra.Ge.to.Gt.relax, 0)

    Eq << Eq[-1].this.expr.apply(Algebra.Gt_0.Gt_0.to.Gt_0)

    Eq <<= Eq.is_positive & Eq[-1]

    Eq << Eq[-1].this.expr.apply(Algebra.Gt_0.Gt_0.to.Gt_0.Add)

    Eq << Imply(Eq[0] & Eq.hypothesis, Eq.induct, plausible=True)

    Eq << Algebra.Cond.Cond.Imply.to.Cond.induct.apply(Eq.initial0, Eq.initial1, Eq[-1], n=n, start=1)

    Eq << Eq[0].subs(n, n + 1)

    Eq << Eq[0].subs(n, n + 2)


if __name__ == '__main__':
    run()

# created on 2020-11-02
