from util import *


@apply
def apply(x):
    n, = x.shape
    assert x.is_real
    return x <= logsumexp(x)


@prove
def prove(Eq):
    from axiom import algebra, keras

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    Eq << apply(x)

    Eq << algebra.le.given.le_zero.apply(Eq[0])

    Eq << Eq[-1].this.lhs.apply(keras.add.logsumexp.to.log.softmax)

    Eq << algebra.le.given.le.exp.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(keras.softmax.to.mul.reducedSum)

    Eq << GreaterEqual(exp(x), ZeroMatrix(*x.shape), plausible=True)

    Eq << algebra.ge_zero.imply.le.reducedSum.apply(Eq[-1])

    Eq << Eq[-1] / Eq[-1].find(ReducedSum)





if __name__ == '__main__':
    run()
# created on 2022-03-31
# updated on 2023-03-25
