from util import *

from axiom.discrete.imply.gt_zero.alpha import alpha


@apply
def apply(A):
    args = A.of(alpha[BlockMatrix])
    return Equal(A, alpha(*args))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    x = Symbol(real=True, positive=True, shape=(oo,))
    y = Symbol(real=True, positive=True)
    n = Symbol(integer=True, positive=True, given=False)
    Eq << apply(alpha(BlockMatrix(x[:n], y)))

    Eq.initial = Eq[0].subs(n, 1)

    Eq << Eq.initial.this.lhs.defun()

    Eq << Eq[-1].this.rhs.defun()

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.defun()

    Eq << Eq[-1].this.rhs.defun()

    Eq << algebra.cond.imply.cond.subs.apply(Eq[0], x[:n], x[1:n + 1])

    Eq << discrete.imply.ne_zero.alpha.apply(Eq[-1].lhs.arg)

    Eq << algebra.ne_zero.eq.imply.eq.inverse.apply(Eq[-1], Eq[-2])

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.cond.infer.imply.cond.induct.apply(Eq.initial, Eq[-1], n=n, start=1)

    


if __name__ == '__main__':
    run()

# created on 2020-09-19
# updated on 2023-05-21
