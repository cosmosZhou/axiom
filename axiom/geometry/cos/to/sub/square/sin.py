from util import *


@apply
def apply(self):
    x = self.of(Cos)
    return Equal(self, 1 - 2 * sin(x / 2) ** 2)


@prove
def prove(Eq):
    from axiom import geometry

    x = Symbol(real=True)
    Eq << apply(cos(x * 2))

    Eq << Eq[0].this.lhs.apply(geometry.cos.to.sub.double)

    Eq << Eq[-1].this.find(cos ** 2).apply(geometry.square.cos.to.sub.square.sin)


if __name__ == '__main__':
    run()
# created on 2023-10-03
