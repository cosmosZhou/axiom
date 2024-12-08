from util import *


@apply
def apply(self):
    x = self.of(sec ** 2)
    return Equal(self, 1 + tan(x) ** 2)


@prove
def prove(Eq):
    from Axiom import Geometry

    x = Symbol(real=True)
    Eq << apply(sec(x) ** 2)

    Eq << Eq[0].this.find(tan ** 2).apply(Geometry.Square.Tan.eq.Sub.Square.Sec)


if __name__ == '__main__':
    run()
# created on 2023-11-26
