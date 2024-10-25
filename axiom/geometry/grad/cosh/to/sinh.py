from util import *


@apply
def apply(self):
    x, (x, S[1]) = self.of(Derivative[cosh])
    return Equal(self, sinh(x))


@prove
def prove(Eq):
    from axiom import geometry

    x = Symbol(real=True)
    Eq << apply(Derivative[x](cosh(x)))

    Eq << Eq[0].this.find(cosh).apply(geometry.cosh.to.add.exp)

    Eq << Eq[-1].this.lhs.doit()

    Eq << Eq[-1].this.rhs.apply(geometry.sinh.to.sub.exp)

    


if __name__ == '__main__':
    run()
# created on 2023-11-26
