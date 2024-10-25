from util import *


@apply
def apply(eq, infer, L):
    A, S[A] = eq.of(Equal[Adjoint])
    x, S[(~x) @ A @ x] = infer.of(Infer[Unequal[0], Expr > 0])
    assert L.is_complex
    return Exists[L](Equal(A, L @ ~L.T))

@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(integer=True, positive=True)
    A = Symbol(shape=(n, n), complex=True)
    x = Symbol(shape=(n,), complex=True)
    L = Symbol(shape=(n, n), complex=True)
    Eq << apply(Equal(~A.T, A),
               Infer(Unequal(x, ZeroMatrix(n)), ~x @ A @ x > 0), L)

    i, j = Symbol(integer=True)
    Eq << discrete.eq_adjoint.infer_gt_zero.then.any.et.Cholesky.apply(*Eq[:2], L, i, j)

    Eq << algebra.any_et.then.any.getitem.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-07-02
