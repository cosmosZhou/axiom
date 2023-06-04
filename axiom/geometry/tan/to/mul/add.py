from util import *


@apply
def apply(self):
    x, y = self.of(tan[Add])
    return Equal(self, (tan(x) + tan(y)) / (1 - tan(x) * tan(y)))


@prove
def prove(Eq):
    from axiom import geometry

    x, y = Symbol(real=True)
    Eq << apply(tan(x + y))

    Eq << Eq[0].this.lhs.apply(geometry.tan.to.mul)

    Eq << Eq[-1].this.find(tan).apply(geometry.tan.to.mul)

    Eq << Eq[-1].this.find(tan).apply(geometry.tan.to.mul)

    Eq << Eq[-1].this.find(tan).apply(geometry.tan.to.mul)

    Eq << Eq[-1].this.find(tan).apply(geometry.tan.to.mul)

    Eq << Eq[-1].this.rhs.ratsimp()

    Eq << Eq[-1].this.find(Sin[Add]).apply(geometry.sin.to.add)

    Eq << Eq[-1].this.find(Cos[Add]).apply(geometry.cos.to.sub)





if __name__ == '__main__':
    run()
# created on 2020-12-06
# updated on 2023-06-01
