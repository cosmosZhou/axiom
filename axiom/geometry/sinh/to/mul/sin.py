from util import *


@apply
def apply(self):
    x = self.of(sinh)
    return Equal(self, -S.ImaginaryUnit * sin(x * S.ImaginaryUnit, evaluate=False))


@prove
def prove(Eq):
    from axiom import geometry

    x = Symbol(real=True)
    Eq << apply(sinh(x))

    Eq << Eq[0].this.find(sin).apply(geometry.sin.to.mul.sinh)

    Eq << Eq[-1].this.rhs.find(sinh).apply(geometry.sinh.to.neg.sinh)




if __name__ == '__main__':
    run()
# created on 2023-11-26
