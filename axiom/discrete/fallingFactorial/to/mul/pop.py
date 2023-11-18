from util import *


@apply
def apply(self):
    x, k = self.of(FallingFactorial)
    assert k > 0 and k.is_integer
    return Equal(self, (x - k + 1) * FallingFactorial(x, k - 1))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    x = Symbol(complex=True)
    k = Symbol(integer=True, positive=True)
    Eq << apply(FallingFactorial(x, k))

    Eq << Eq[0].this.lhs.apply(discrete.fallingFactorial.to.prod)

    Eq << Eq[-1].this.find(FallingFactorial).apply(discrete.fallingFactorial.to.prod)

    Eq << Eq[-1].this.lhs.apply(algebra.prod.to.mul.pop)

    
    


if __name__ == '__main__':
    run()
# created on 2023-08-17
# updated on 2023-08-26
