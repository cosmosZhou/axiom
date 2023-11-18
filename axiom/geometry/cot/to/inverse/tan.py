from util import *


@apply
def apply(self):
    x = self.of(cot)
    return Equal(self, 1 / tan(x))


@prove
def prove(Eq):
    from axiom import geometry

    x = Symbol(real=True)
    Eq << apply(cot(x))

    Eq << Eq[0].this.lhs.apply(geometry.cot.to.div)

    Eq << Eq[-1].this.find(tan).apply(geometry.tan.to.div)


if __name__ == '__main__':
    run()
# created on 2023-10-03
