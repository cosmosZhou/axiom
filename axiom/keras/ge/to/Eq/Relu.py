from util import *


@apply
def apply(ge):
    i, l = ge.of(GreaterEqual)
    return Equal(relu(i + 1 - l), i + 1 - l)


@prove
def prove(Eq):
    from Axiom import Keras, Algebra

    i, l = Symbol(integer=True)
    Eq << apply(i >= l)

    Eq << Eq[1].this.lhs.apply(Keras.Relu.eq.Add.Min)

    Eq << Algebra.Ge.to.Gt.relax.apply(Eq[0], upper=i + 1)

    Eq << Algebra.Gt.to.Eq.Min.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2022-04-01
