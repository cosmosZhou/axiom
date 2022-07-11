from util import *


@apply
def apply(self):
    z = self.of(Re)

    return Equal(self, abs(z) * cos(Arg(z)))


@prove
def prove(Eq):
    from axiom import geometry, algebra

    z = Symbol(complex=True, given=True)
    Eq << apply(Re(z))

    Eq << Eq[0].this.find(cos).apply(geometry.cos_arg.to.piece)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.piece)

    Eq << Eq[-1].this.find(Abs).apply(algebra.abs.to.sqrt)

    


if __name__ == '__main__':
    run()
# created on 2018-06-13
# updated on 2022-01-23
