from util import *


@apply
def apply(self):
    x, k = self.of(RisingFactorial)
    assert k > 0
    return Equal(self, (x + k - 1) * RisingFactorial(x, k - 1))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    x = Symbol(complex=True)
    k = Symbol(integer=True, positive=True)
    Eq << apply(RisingFactorial(x, k))

    Eq << Eq[0].this.lhs.apply(discrete.risingFactorial.to.prod)

    Eq << Eq[-1].this.find(RisingFactorial).apply(discrete.risingFactorial.to.prod)

    Eq << Eq[-1].this.lhs.apply(algebra.prod.to.mul.pop)

    


if __name__ == '__main__':
    run()
# created on 2023-08-17
