from util import *


@apply
def apply(x):
    n, = x.shape
    assert x.is_real
    return x <= logsumexp(x)


@prove
def prove(Eq):
    from Axiom import Algebra, Keras

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    Eq << apply(x)

    Eq << Algebra.Le.of.Le_0.apply(Eq[0])

    Eq << Eq[-1].this.lhs.apply(Keras.Add.LogSumExp.eq.Log.Softmax)

    Eq << Algebra.Le.of.Le.Exp.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Keras.Softmax.eq.Mul.ReducedSum)

    Eq << GreaterEqual(exp(x), ZeroMatrix(*x.shape), plausible=True)

    Eq << Algebra.Ge_0.to.Le.ReducedSum.apply(Eq[-1])

    Eq << Eq[-1] / Eq[-1].find(ReducedSum)


if __name__ == '__main__':
    run()
# created on 2022-03-31
# updated on 2023-03-25
