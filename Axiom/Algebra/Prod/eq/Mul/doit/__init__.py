from util import *


@apply
def apply(self):
    from Axiom.Algebra.Sum.eq.Add.doit import doit
    return Equal(self, doit(Product, self))


@prove
def prove(Eq):
    from Axiom import Algebra

    k = Symbol(integer=True, positive=True)
    n = 5
    x = Symbol(real=True, shape=(n, k))
    i = Symbol(integer=True)
    Eq << apply(Product[i](x[i]))

    Eq << Eq[-1].this.lhs.apply(Algebra.Prod.limits.domain_defined)

    n -= 1
    Eq << Eq[-1].this.lhs.apply(Algebra.Prod.eq.Mul.split, cond={n})

    n -= 1
    Eq << Eq[-1].this.find(Product).apply(Algebra.Prod.eq.Mul.split, cond={n})

    n -= 1
    Eq << Eq[-1].this.find(Product).apply(Algebra.Prod.eq.Mul.split, cond={n})

    n -= 1
    Eq << Eq[-1].this.find(Product).apply(Algebra.Prod.eq.Mul.split, cond={n})


if __name__ == '__main__':
    run()

# created on 2020-03-04
from . import outer
from . import setlimit
