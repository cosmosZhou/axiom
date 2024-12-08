from util import *


@apply
def apply(lt):
    i, l = lt.of(Less)
    return Equal(relu(i + 1 - l), 0)


@prove
def prove(Eq):
    from Axiom import Keras, Algebra

    i, l = Symbol(integer=True)
    Eq << apply(i < l)

    Eq << Eq[1].this.lhs.apply(Keras.Relu.eq.Add.Min)

    Eq << Algebra.Lt.to.Le.strengthen.plus.apply(Eq[0])

    Eq << Algebra.Le.to.Eq.Min.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2022-04-01
