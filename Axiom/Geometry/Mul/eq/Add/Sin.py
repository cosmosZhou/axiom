from util import *


@apply
def apply(self):
    x, y = self.of(Sin * Cos)
    return Equal(self, (sin(x + y) + sin(x - y)) / 2)


@prove
def prove(Eq):
    from Axiom import Geometry

    x, y = Symbol(real=True)
    Eq << apply(sin(x) * cos(y))

    Eq << Eq[-1].this.find(Sin[Expr - Expr]).apply(Geometry.Sin.eq.Add)

    Eq << Eq[-1].this.find(Sin[Expr + Expr]).apply(Geometry.Sin.eq.Add)




if __name__ == '__main__':
    run()
# created on 2020-12-02
# updated on 2023-06-01
