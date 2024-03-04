from util import *


@apply
def apply(self):
    x = self.of(cosh)
    return Equal(self, cos(x * S.ImaginaryUnit, evaluate=False))


@prove
def prove(Eq):
    from axiom import geometry

    x = Symbol(real=True)
    Eq << apply(cosh(x))

    Eq << Eq[0].this.rhs.apply(geometry.cos.to.cosh)

    Eq << Eq[-1].this.rhs.apply(geometry.cosh.neg)

    


if __name__ == '__main__':
    run()
# created on 2023-11-26
