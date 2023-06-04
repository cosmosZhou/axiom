from util import *


@apply
def apply(self):
    (x, d), S[d] = self.of(Floor[Expr / Expr] * Expr)
    assert d.is_integer and x.is_integer
    return Equal(self, x - x % d)


@prove
def prove(Eq):
    from axiom import algebra
    x, d = Symbol(integer=True)
    Eq << apply(x // d * d)

    Eq << algebra.mod.to.sub.apply(x % d)

    Eq << Eq[0] - Eq[1]


if __name__ == '__main__':
    run()
# created on 2020-01-28
