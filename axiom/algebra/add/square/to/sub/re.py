from util import *


@apply
def apply(self):
    args = self.of(Add)
    args = [arg.of(Abs ** 2) for arg in args]
    from axiom.algebra.square.abs.to.add.re import sigmar2
    return Equal(self, Abs(Add(*args)) ** 2 - sigmar2(args))


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(complex=True)
    Eq << apply(abs(x) ** 2 + abs(y) ** 2 + abs(z) ** 2)

    Eq << Eq[0].this.find(Abs[Add] ** 2).apply(algebra.square.abs.to.add.re)


if __name__ == '__main__':
    run()
# created on 2023-06-24
