from util import *


from axiom.discrete.K.to.add.definition import K
@apply
def apply(given):
    (x, j), (S[j], n) = given.of(All[Indexed > 0, Tuple[1, Expr]])
    return Greater(K(x[:n]), 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, shape=(oo,))
    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    Eq << apply(All[i:1:n](x[i] > 0))

    Eq.hypothesis = Infer(Eq[0], Eq[1], plausible=True)

    Eq.initial0 = Eq.hypothesis.subs(n, 1)

    Eq << Eq.initial0.this.lhs.defun()

    Eq.initial1 = Eq.hypothesis.subs(n, 2)

    Eq << Eq.initial1.this.find(K).defun()

    Eq.induct2 = Eq.hypothesis.subs(n, n + 2)

    Eq << Eq.induct2.this.find(K).defun()

    Eq.induct1 = Eq.hypothesis.subs(n, n + 1)

    Eq << Eq.induct1.this.lhs.apply(algebra.all.given.all.limits.relax, Range(1, n + 2))

    Eq << algebra.infer_et.imply.infer.et.apply(Eq[-1])

    Eq << Eq[-1].this.find(And, All).apply(algebra.all.imply.cond.subs, Eq[-1].lhs.variable, n + 1)

    Eq << Eq[-1].this.find(And).apply(algebra.gt_zero.gt_zero.imply.gt_zero)

    Eq << Eq.hypothesis.this.lhs.apply(algebra.all.given.all.limits.relax, Range(1, n + 2))

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.find(And).apply(algebra.gt_zero.gt_zero.imply.gt_zero.add)

    Eq << Infer(Eq.hypothesis & Eq.induct1, Eq.induct2, plausible=True)

    Eq << algebra.cond.cond.infer.imply.cond.induct.apply(Eq.initial0, Eq.initial1, Eq[-1], n=n, start=1)

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq.hypothesis)
    Eq << Eq.hypothesis.subs(n, n + 1)
    Eq << Eq.hypothesis.subs(n, n + 2)

    
    


if __name__ == '__main__':
    run()

# created on 2020-09-15
# updated on 2023-05-21
