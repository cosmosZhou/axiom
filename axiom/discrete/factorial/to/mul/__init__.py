from util import *


@apply
def apply(self):
    n = self.of(Factorial)
    assert n > 0
    return Equal(self, n * factorial(n - 1))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(integer=True, positive=True)
    Eq << apply(factorial(n))

    Eq << Eq[0].this.find(factorial).apply(discrete.factorial.to.prod)

    Eq << Eq[-1].this.find(factorial).apply(discrete.factorial.to.prod)

    Eq << Eq[-1].this.lhs.apply(algebra.prod.to.mul.split, cond={n})


if __name__ == '__main__':
    run()
# created on 2020-08-06
del factorial2
from . import factorial2
