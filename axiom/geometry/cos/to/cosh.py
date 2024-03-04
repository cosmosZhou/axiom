from util import *


@apply
def apply(self):
    x = self.of(cos)
    return Equal(self, cosh(x * S.ImaginaryUnit, evaluate=False))


@prove
def prove(Eq):
    from axiom import geometry

    x = Symbol(real=True)
    Eq << apply(cos(x))

    Eq << Eq[-1].this.rhs.apply(geometry.cosh.to.add.exp)

    Eq << Eq[-1].this.lhs.apply(geometry.cos.to.add.expi)


if __name__ == '__main__':
    run()
# created on 2023-11-26
