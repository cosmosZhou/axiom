from util import *


@apply
def apply(self):
    arg = self.of(Abs)
    return Equal(self, Abs(~arg, evaluate=False))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(complex=True)
    Eq << apply(Abs(x + ~y))

    Eq << Eq[0].this.lhs.apply(algebra.abs.to.sqrt)

    Eq << Eq[-1].this.rhs.apply(algebra.abs.to.sqrt)

    Eq << Eq[-1].this.rhs.find((Expr - Expr) ** 2).apply(algebra.square.negate)

    


if __name__ == '__main__':
    run()
# created on 2023-06-24
