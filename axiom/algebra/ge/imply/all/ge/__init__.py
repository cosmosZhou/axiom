from util import *


@apply
def apply(ge, var=None):
    from axiom.algebra.le.given.all.le import all_getitem
    return all_getitem(ge, GreaterEqual, var=var)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n,), real=True)
    Eq << apply(x >= y)

    Eq << Eq[0].this.apply(algebra.ge.to.all.ge)

    


if __name__ == '__main__':
    run()
# created on 2022-03-31
# updated on 2022-04-01
from . import monotone
