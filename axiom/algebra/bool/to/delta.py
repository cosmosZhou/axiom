from util import *


@apply
def apply(self):
    x, y = self.of(Bool[Equal])
    return Equal(self, KroneckerDelta(x, y))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply(Bool(Equal(x, y)))

    Eq << Eq[0].this.rhs.apply(algebra.delta.to.bool)


if __name__ == '__main__':
    run()
# created on 2023-08-20
