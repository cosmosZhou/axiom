from util import *


@apply
def apply(A):
    from Axiom.Discrete.Alpha.gt.Zero import alpha

    args = A.of(alpha[BlockMatrix])
    return Equal(A, alpha(*args))


@prove
def prove(Eq):
    from Axiom import Algebra, Discrete, Logic
    from Axiom.Discrete.Alpha.gt.Zero import alpha

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

    Eq << Algebra.Cond.of.Cond.subs.apply(Eq[0], x[:n], x[1:n + 1])

    Eq << Discrete.Alpha.ne.Zero.apply(Eq[-1].lhs.arg)

    Eq << Algebra.EqInv.of.Ne_0.Eq.apply(Eq[-1], Eq[-2])

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Logic.Cond.of.Cond.Imp.induct.apply(Eq.initial, Eq[-1], n=n, start=1)




if __name__ == '__main__':
    run()

# created on 2020-09-19
# updated on 2023-05-21
