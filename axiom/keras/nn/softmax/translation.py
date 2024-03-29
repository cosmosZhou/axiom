from util import *


@apply
def apply(x, delta):
    n, = x.shape
    assert not delta.shape

    return Equal(softmax(x + delta), softmax(x))


@prove
def prove(Eq):
    from axiom import keras, algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    delta = Symbol(real=True)
    Eq << apply(x, delta)

    Eq << Eq[-1].this.lhs.apply(keras.softmax.to.mul.reducedSum)

    Eq << Eq[-1].this.find(ReducedSum[~Exp]).apply(algebra.exp.to.mul)

    Eq << Eq[-1].this.lhs.powsimp()

    Eq << Eq[-1].this.rhs.apply(keras.softmax.to.mul.reducedSum)

    


if __name__ == '__main__':
    run()
# created on 2021-01-05
# updated on 2022-10-04
