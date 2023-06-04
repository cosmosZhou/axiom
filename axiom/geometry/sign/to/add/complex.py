from util import *


@apply
def apply(self):
    x = self.of(Sign)
    assert x.is_nonzero
    return Equal(self, cos(Arg(x)) + S.ImaginaryUnit * sin(Arg(x)))


@prove
def prove(Eq):
    from axiom import algebra, geometry

    z = Symbol(complex=True, zero=False)
    Eq << apply(Sign(z))

    Eq << Eq[-1].this.lhs.apply(algebra.sign.to.expi.arg)

    Eq << Eq[-1].this.lhs.apply(geometry.expi.to.add.Euler)

    


if __name__ == '__main__':
    run()
# created on 2023-05-25
