from util import *


@apply
def apply(self):
    from axiom.algebra.sum.to.add.doit import doit
    return doit(All, self)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True, shape=(oo,))
    i = Symbol(integer=True)

    n = 5
    Eq << apply(All[i:n](x[i] > 0))

    n -= 1
    Eq << Eq[-1].this.find(All).apply(algebra.all.to.et.split, cond={n})

    n -= 1
    Eq << Eq[-1].this.find(All).apply(algebra.all.to.et.split, cond={n})

    n -= 1
    Eq << Eq[-1].this.find(All).apply(algebra.all.to.et.split, cond={n})

    n -= 1
    Eq << Eq[-1].this.find(All).apply(algebra.all.to.et.split, cond={n})


if __name__ == '__main__':
    run()
from . import outer
from . import setlimit
# created on 2018-04-24
