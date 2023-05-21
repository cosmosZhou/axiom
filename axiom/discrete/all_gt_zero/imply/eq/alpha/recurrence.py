from util import *


@apply
def apply(given):
    (x, j), (S[j], n) = given.of(All[Indexed > 0, Tuple[1, Expr]])
    n = n - 2
    return Equal(alpha(x[:n + 2]), alpha(x[:n], x[n] + 1 / x[n + 1]))


from axiom.discrete.imply.gt_zero.alpha import alpha


@prove
def prove(Eq):
    from axiom import algebra, discrete

    x = Symbol(real=True, shape=(oo,))
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    Eq << apply(All[i:1:n + 2](x[i] > 0))

    Eq.hypothesis = Infer(Eq[0], Eq[1], plausible=True)
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
    
    Eq << algebra.cond.imply.cond.subs.apply(Eq.hypothesis, x[:n + 2], x[1:n + 3])
    
    Eq << Eq[-1].this.lhs.apply(algebra.all.limits.subs.offset, -1)
    
    Eq << Eq[-1].this.lhs.apply(algebra.all.given.all.limits.relax, domain=Range(1, n + 3))
    
    
    Eq << Infer(All[i:1:n + 3](x[i] > 0), Unequal(alpha(x[1:n + 3]), 0), plausible=True)
    
    Eq << Eq[-1].this.lhs.apply(discrete.all_gt_zero.imply.ne_zero.alpha.offset)
    
    Eq <<= Eq[-1] & Eq[-2]
    
    Eq << Eq[-1].this.rhs.apply(algebra.ne_zero.eq.imply.eq.inverse)
    
    Eq << Infer(Eq.hypothesis, Eq.induct, plausible=True)
    
    Eq << algebra.cond.infer.imply.cond.induct.apply(Eq.initial, Eq[-1], n=n, start=1)
    

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq.hypothesis)

    


if __name__ == '__main__':
    run()

# created on 2020-09-24
# updated on 2023-05-21
