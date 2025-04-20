from util import *


@apply
def apply(self):
    matmul, (j, *j_ab) = self.of(Lamda)
    if j_ab:
        S[0], k = j_ab
    else:
        S[0], k = matmul.domain_defined(j).of(Range)

    A, B = matmul.of(MatMul)

    if A._has(j):
        A = Lamda[j:k](A).simplify()

        if B._has(j):
            B = Lamda[j:k](B).simplify()
            assert A.shape[-1] == B.shape[-2]

    else:
        assert B._has(j)
        i = B.generate_var(excludes=j, integer=True)
        n = B.shape[0]
        B = Lamda[j:k, i:n](B[i]).simplify()

    return Equal(self, A @ B, evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra

    i = Symbol(integer=True)
    n, m = Symbol(integer=True, positive=True)
    k = Symbol(domain=Range(1, m + 1))
    Q = Symbol(shape=(n, n), real=True)
    K = Symbol(shape=(m, n, n), real=True)
    Eq << apply(Lamda[i:k](Q[i] @ K[i]))

    j = Symbol(domain=Range(k))
    Eq << Algebra.Eq.given.Eq.getitem.apply(Eq[0], j)





if __name__ == '__main__':
    run()

# created on 2020-08-17
# updated on 2022-01-11