from util import *


@apply
def apply(self):
    A, B = self.of(Exp @ Exp)
    if len(A.shape) < len(B.shape):
        rhs = ReducedSum(exp(A + B.T))
    elif len(A.shape) > len(B.shape):
        rhs = ReducedSum(exp(A + B))
    else:
        return

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Axiom import Discrete, Algebra

    n, k, m = Symbol(integer=True, positive=True)

    A = Symbol(shape=(k, m), complex=True)
    B = Symbol(shape=(m,), complex=True)

    # A = Symbol(shape=(m,), complex=True)
    # B = Symbol(shape=(m, n), complex=True)
    Eq << apply(exp(A) @ exp(B))

    Eq << Eq[-1].this.lhs.apply(Discrete.Dot.eq.Lamda)

    Eq << Eq[-1].this.rhs.apply(Algebra.ReducedSum.eq.Lamda, var=Eq[1].lhs.expr.variable)

    Eq << Eq[-1].this.rhs.simplify()

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.ExpAdd.eq.MulExpS)


if __name__ == '__main__':
    run()
# created on 2020-11-11
