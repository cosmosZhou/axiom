from util import *


@apply
def apply(self):
    x, (x, S[1]) = self.of(Derivative[tan])
    return Equal(self, sec(x) ** 2)


@prove
def prove(Eq):
    from axiom import geometry, calculus

    x = Symbol(real=True)
    Eq << apply(Derivative[x](tan(x)))

    Eq << Eq[0].this.find(tan).apply(geometry.tan.to.div)

    Eq << Eq[-1].this.lhs.apply(calculus.grad.div.to.div.sub)

    Eq << Eq[-1].this.find(Derivative).doit()

    Eq << Eq[-1].this.find(Derivative).doit()

    Eq << Eq[-1].this.find(cos ** 2).apply(geometry.square.cos.to.sub.square.sin)

    Eq << Eq[-1].this.find(cos).apply(geometry.cos.to.inverse.sec)
    


if __name__ == '__main__':
    run()
# created on 2023-11-26
