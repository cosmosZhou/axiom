from util import *


@apply
def apply(self):
    from axiom.algebra.sum.limits.domain_defined import limits_insert
    assert self.is_Cup
    return Equal(self, limits_insert(self))


@prove
def prove(Eq):
    from axiom import sets
    i, j = Symbol(integer=True)
    k = Symbol(integer=True, positive=True)
    x = Symbol(shape=(k,), integer=True)

    f = Function(etype=dtype.integer)
    h = Function(etype=dtype.real)

    Eq << apply(Cup[j:f(i), i](h(x[i], j)))

    Eq << Eq[-1].this.rhs.apply(sets.cup.limits.domain_defined.delete)


if __name__ == '__main__':
    run()

# created on 2020-07-25

from . import delete
