from util import *


@apply
def apply(self):
    (x, k), S[x - k] = self.of(FallingFactorial * Expr)
    k += 1
    assert k > 0
    return Equal(self, FallingFactorial(x, k))


@prove
def prove(Eq):
    from axiom import discrete
    
    x = Symbol(complex=True)
    k = Symbol(integer=True, positive=True)
    Eq << apply((x - k + 1) * FallingFactorial(x, k - 1))
    
    Eq << Eq[0].this.rhs.apply(discrete.fallingFactorial.to.mul.pop)


if __name__ == '__main__':
    run()
# created on 2023-08-17
