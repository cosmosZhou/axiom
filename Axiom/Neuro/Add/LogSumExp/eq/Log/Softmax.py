from util import *


@apply
def apply(self):
    x, S[x] = self.of(Expr - logsumexp)
    n, = x.shape
    return Equal(self, log(softmax(x)))


@prove
def prove(Eq):
    from Axiom import Neuro

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    Eq << apply(x - logsumexp(x))

    Eq << Eq[0].this.rhs.apply(Neuro.Log.Softmax.eq.Add.LogSumExp)


if __name__ == '__main__':
    run()
# created on 2022-03-31
