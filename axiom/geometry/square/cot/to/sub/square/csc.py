from util import *


@apply
def apply(self):
    x = self.of(Cot ** 2)
    return Equal(self, csc(x) ** 2 - 1)


@prove
def prove(Eq):
    from axiom import geometry, algebra

    x = Symbol(real=True)
    Eq << apply(cot(x) ** 2)

    Eq << Eq[0].this.find(cot).apply(geometry.cot.to.div)

    Eq << Eq[-1].this.find(cos ** 2).apply(geometry.square.cos.to.sub.square.sin)

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(csc).apply(geometry.csc.to.inverse.sin)


if __name__ == '__main__':
    run()
# created on 2023-10-03
