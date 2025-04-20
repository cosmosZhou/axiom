from util import *


@apply
def apply(self):
    ((Q, t), (((V, KT), i), (S[i], S[0], T))), (S[t], S[0], S[T]) = self.of(Lamda[sigmoid[Indexed] * Sum[Indexed[Symbol * Transpose[Softmax]]]])
    return Equal(self, sigmoid(Q) * ReducedSum(softmax(KT) * V.T))


@prove
def prove(Eq):
    from Axiom import Algebra

    T, d = Symbol(integer=True, positive=True)
    i, t = Symbol(integer=True)
    Q, K, V = Symbol(shape=(T, d), real=True)
    Eq << apply(
        Lamda[t:T](sigmoid(Q[t]) * Sum[i:T](Indexed(softmax(K.T).T * V, i))))

    t = Symbol(domain=Range(T))
    Eq << Algebra.Eq.given.Eq.getitem.apply(Eq[0], t)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.ReducedSum)

    # https://arxiv.org/pdf/2105.14103.pdf


if __name__ == '__main__':
    run()
# created on 2023-09-15
