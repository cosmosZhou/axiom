from util import *


@apply
def apply(self):
    x = self.of(sin)
    return Equal(self, -S.ImaginaryUnit * sinh(x * S.ImaginaryUnit, evaluate=False))


@prove
def prove(Eq):
    from axiom import geometry

    x = Symbol(real=True)
    Eq << apply(sin(x))

    Eq << Eq[0].this.find(sinh).apply(geometry.sinh.to.sub.exp)

    Eq << Eq[-1].this.lhs.apply(geometry.sin.to.add.expi)


if __name__ == '__main__':
    run()
# created on 2023-11-26
