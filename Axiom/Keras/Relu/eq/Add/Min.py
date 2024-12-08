from util import *


@apply
def apply(self):
    y, x = self.of(relu[Expr - Expr])

    return Equal(self, y - Min(x, y))


@prove
def prove(Eq):
    from Axiom import Keras

    x, y = Symbol(real=True)
    Eq << apply(relu(y - x))

    Eq << Eq[0].this.find(Min).apply(Keras.Min.eq.Add.Relu)









if __name__ == '__main__':
    run()
# created on 2021-12-15
