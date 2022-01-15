from util import *


def doit(Sum, self):
    xi, (i, a, b), *limits = self.of(Sum[Tuple])
    assert i.is_integer

    diff = b - a
    assert diff == int(diff)

    sgm = Sum.identity(xi)
    for t in range(diff):
        sgm = Sum.operator(sgm, xi._subs(i, a + t))

    return Sum(sgm, *limits)


@apply
def apply(self):
    return Equal(self, doit(Sum, self))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True, shape=(oo, oo))
    i, j = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)

    n = 5
    Eq << apply(Sum[j:n, i:m](x[i, j]))

    s = Symbol(Lamda[i](Sum[j:n](x[i, j])))

    Eq << s[i].this.definition

    Eq << algebra.eq.imply.eq.sum.apply(Eq[-1], (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(algebra.sum.to.add.doit)

    Eq << Eq[-2].subs(Eq[-1]).reversed


if __name__ == '__main__':
    run()

from . import setlimit
# created on 2018-04-30
