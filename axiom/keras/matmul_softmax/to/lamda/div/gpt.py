from util import *


@apply
def apply(self, i, j):
    (((Q, KT), d_sqrt), ((_n,), (S[0],))), V = self.of(Softmax[Expr @ Expr / Expr + (BandPart[OneMatrix] - 1) * Infinity] @ Expr)
    n = V.shape[0]
    assert _n >= n - 1
    K = KT.T
    return Equal(self, Lamda[i:n](Sum[j:i + 1](V[j] * Exp((Q[i] @ K[j]) / d_sqrt)) / ReducedSum(Exp((Q[i] @ K[:i + 1].T) / d_sqrt))))


@prove
def prove(Eq):
    from axiom import keras, discrete

    n, d_z = Symbol(integer=True, positive=True)
    i, j = Symbol(integer=True)
    Q, K, V = Symbol(shape=(n, d_z), real=True)
    Eq << apply(softmax(Q @ K.T / sqrt(d_z) + (BandPart[n, 0](OneMatrix(n, n)) - 1) * oo) @ V, i, j)

    Eq << Eq[0].this.lhs.apply(keras.matmul_softmax.to.lamda.matmul.gpt, i)

    Eq << Eq[-1].this.lhs.apply(discrete.matmul.to.sum)

    


if __name__ == '__main__':
    run()
# created on 2023-06-18
