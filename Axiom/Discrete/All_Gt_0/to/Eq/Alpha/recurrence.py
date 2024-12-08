from util import *


@apply
def apply(given):
    from Axiom.Discrete.Alpha.gt.Zero import alpha

    (x, j), (S[j], n) = given.of(All[Indexed > 0, Tuple[1, Expr]])
    n = n - 2
    return Equal(alpha(x[:n + 2]), alpha(x[:n], x[n] + 1 / x[n + 1]))


@prove
def prove(Eq):
    from Axiom import Algebra, Discrete
    from Axiom.Discrete.Alpha.gt.Zero import alpha

    x = Symbol(real=True, shape=(oo,))
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    Eq << apply(All[i:1:n + 2](x[i] > 0))

    Eq.hypothesis = Imply(Eq[0], Eq[1], plausible=True)

    Eq.initial = Eq.hypothesis.subs(n, 1)

    Eq << Eq.initial.this.lhs.doit()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq << Eq.induct.this.find(alpha).defun()

    Eq << Eq[-1].this.rhs.rhs.defun()

    Eq << Algebra.Cond.to.Cond.subs.apply(Eq.hypothesis, x[:n + 2], x[1:n + 3])

    Eq << Eq[-1].this.lhs.apply(Algebra.All.limits.subs.offset, -1)

    Eq << Eq[-1].this.lhs.apply(Algebra.All.of.All.limits.relax, Range(1, n + 3))

    Eq << Imply(All[i:1:n + 3](x[i] > 0), Unequal(alpha(x[1:n + 3]), 0), plausible=True)

    Eq << Eq[-1].this.lhs.apply(Discrete.All_Gt_0.to.Ne_0.Alpha.offset)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Algebra.Ne_0.Eq.to.Eq.Inv)

    Eq << Imply(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << Algebra.Cond.Imply.to.Cond.induct.apply(Eq.initial, Eq[-1], n=n, start=1)

    Eq << Algebra.Cond.Imply.to.Cond.trans.apply(Eq[0], Eq.hypothesis)





if __name__ == '__main__':
    run()

# created on 2020-09-24
# updated on 2023-11-12
