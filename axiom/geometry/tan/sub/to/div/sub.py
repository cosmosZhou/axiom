from util import *


@apply
def apply(self):
    x, y = self.of(tan[Expr - Expr])
    return Equal(self, (tan(x) - tan(y)) / (1 + tan(x) * tan(y)))


@prove
def prove(Eq):
    from axiom import geometry

    x, y = Symbol(real=True)
    Eq << apply(tan(x - y))

    Eq << Eq[-1].this.lhs.apply(geometry.tan.add.to.div)


if __name__ == '__main__':
    run()
# created on 2023-06-01
