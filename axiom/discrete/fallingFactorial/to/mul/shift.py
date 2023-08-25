from util import *


@apply
def apply(self):
    x, k = self.of(FallingFactorial)
    assert k > 0
    return Equal(self, x * FallingFactorial(x - 1, k - 1))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    x = Symbol(complex=True)
    k = Symbol(integer=True, positive=True)
    Eq << apply(FallingFactorial(x, k))

    Eq << Eq[0].this.lhs.apply(discrete.fallingFactorial.to.prod)

    Eq << Eq[-1].this.find(FallingFactorial).apply(discrete.fallingFactorial.to.prod)

    Eq << Eq[-1].this.lhs.apply(algebra.prod.to.mul.shift)

    Eq << Eq[-1].this.rhs.find(Product).apply(algebra.prod.limits.subs.offset, -1)

    


if __name__ == '__main__':
    run()
# created on 2023-08-17
