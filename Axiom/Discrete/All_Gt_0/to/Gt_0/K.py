from util import *


@apply
def apply(given):
    from Axiom.Discrete.K.eq.Add.definition import K

    (x, j), (S[j], n) = given.of(All[Indexed > 0, Tuple[1, Expr]])
    return Greater(K(x[:n]), 0)


@prove
def prove(Eq):
    from Axiom import Algebra
    from Axiom.Discrete.K.eq.Add.definition import K
    x = Symbol(real=True, shape=(oo,))
    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    Eq << apply(All[i:1:n](x[i] > 0))

    Eq.hypothesis = Imply(Eq[0], Eq[1], plausible=True)

    Eq.initial0 = Eq.hypothesis.subs(n, 1)

    Eq << Eq.initial0.this.lhs.defun()

    Eq.initial1 = Eq.hypothesis.subs(n, 2)

    Eq << Eq.initial1.this.find(K).defun()

    Eq.induct2 = Eq.hypothesis.subs(n, n + 2)

    Eq << Eq.induct2.this.find(K).defun()

    Eq.induct1 = Eq.hypothesis.subs(n, n + 1)

    Eq << Eq.induct1.this.lhs.apply(Algebra.All.of.All.limits.relax, Range(1, n + 2))

    Eq << Algebra.Imply_And.to.Imply.And.apply(Eq[-1])

    Eq << Eq[-1].this.find(And, All).apply(Algebra.All.to.Cond.subs, Eq[-1].lhs.variable, n + 1)

    Eq << Eq[-1].this.find(And).apply(Algebra.Gt_0.Gt_0.to.Gt_0)

    Eq << Eq.hypothesis.this.lhs.apply(Algebra.All.of.All.limits.relax, Range(1, n + 2))

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.find(And).apply(Algebra.Gt_0.Gt_0.to.Gt_0.Add)

    Eq << Imply(Eq.hypothesis & Eq.induct1, Eq.induct2, plausible=True)

    Eq << Algebra.Cond.Cond.Imply.to.Cond.induct.apply(Eq.initial0, Eq.initial1, Eq[-1], n=n, start=1)

    Eq << Algebra.Cond.Imply.to.Cond.trans.apply(Eq[0], Eq.hypothesis)
    Eq << Eq.hypothesis.subs(n, n + 1)
    Eq << Eq.hypothesis.subs(n, n + 2)





if __name__ == '__main__':
    run()

# created on 2020-09-15
# updated on 2023-05-21