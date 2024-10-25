from util import *


@apply
def apply(self):
    x, y = self.of(Equal)

    return Equal(x - y, 0)


@prove
def prove(Eq):
    from axiom import algebra

    a = Symbol(real=True)
    b = Symbol(real=True, zero=False)
    Eq << apply(Equal(a, b))

    Eq << algebra.iff.of.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.eq.then.is_zero)

    Eq << Eq[-1].this.lhs.apply(algebra.eq.of.is_zero)


if __name__ == '__main__':
    run()
# created on 2021-12-29
