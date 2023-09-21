from util import *


@apply
def apply(eq_ab, eq_cd):
    (A, B), X = eq_ab.of(Equal[MatMul])
    (C, D), Y = eq_cd.of(Equal[MatMul])

    return Equal(S[
        [                                 A, ZeroMatrix(A.shape[0], C.shape[1])], 
        [ZeroMatrix(C.shape[0], A.shape[1]),                                  C]] @ [
        [                                 B, ZeroMatrix(B.shape[0], D.shape[1])], 
        [ZeroMatrix(D.shape[0], B.shape[1]),                                  D]], [
        [                                 X, ZeroMatrix(X.shape[0], Y.shape[1])],
        [ZeroMatrix(Y.shape[0], X.shape[1]),                                  Y]])


@prove
def prove(Eq):
    from axiom import discrete

    n = Symbol(integer=True, positive=True)
    A, B, C, D, X, Y = Symbol(shape=(n, n), real=True)
    Eq << apply(Equal(A @ B, X), Equal(C @ D, Y))

    Eq << Eq[-1].this.lhs.apply(discrete.matmul.to.block, deep=True)

    Eq << Eq[-1].subs(*Eq[:2])


if __name__ == '__main__':
    run()
# created on 2023-09-16
