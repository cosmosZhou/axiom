from util import *


@apply
def apply(self):
    y, x = self.of(Sin * Cos)
    return Equal(self, (sin(x + y) - sin(x - y)) / 2)


@prove
def prove(Eq):
    from axiom import geometry

    x, y = Symbol(real=True)
    Eq << apply(sin(y) * cos(x))

    Eq << Eq[-1].this.find(Sin[Expr - Expr]).apply(geometry.sin.to.add)

    Eq << Eq[-1].this.find(Sin[Expr + Expr]).apply(geometry.sin.to.add)


if __name__ == '__main__':
    run()
# created on 2023-06-01
