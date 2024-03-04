from util import *


@apply
def apply(self):
    x, (x, S[1]) = self.of(Derivative[tanh])
    return Equal(self, sech(x) ** 2)


@prove
def prove(Eq):
    from axiom import geometry, calculus, algebra

    x = Symbol(real=True)
    Eq << apply(Derivative[x](tanh(x)))

    Eq << Eq[0].this.find(tanh).apply(geometry.tanh.to.div)

    Eq << Eq[-1].this.lhs.apply(calculus.grad.div.to.div.sub)

    Eq << Eq[-1].this.find(Derivative).apply(geometry.grad.sinh.to.cosh)

    Eq << Eq[-1].this.find(Derivative).apply(geometry.grad.cosh.to.sinh)

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(sinh).apply(geometry.sinh.to.mul.tanh)

    Eq << Eq[-1].this.rhs.apply(geometry.square.sech.to.sub.square.tanh)


if __name__ == '__main__':
    run()
# created on 2023-11-26
