from util import *


@apply
def apply(self):
    x = self.of(sec ** 2)
    return Equal(self, 1 + tan(x) ** 2)


@prove
def prove(Eq):
    from axiom import geometry

    x = Symbol(real=True)
    Eq << apply(sec(x) ** 2)

    Eq << Eq[0].this.find(tan ** 2).apply(geometry.square.tan.to.sub.square.sec)


if __name__ == '__main__':
    run()
# created on 2023-11-26
