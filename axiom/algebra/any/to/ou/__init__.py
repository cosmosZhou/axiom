from util import *


@apply(given=None)
def apply(self, simplify=True):
    from axiom.algebra.sum.to.add import associate
    return Equivalent(self, associate(Any, self, simplify=simplify))


@prove
def prove(Eq):
    from axiom import algebra
    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)

    f, h = Function(real=True)

    Eq << apply(Any[i:n]((f(i) > 0) | (h(i) > 0)))

    Eq << algebra.iff.given.et.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(algebra.any_ou.imply.ou.any)

    Eq << Eq[-1].this.lhs.apply(algebra.any_ou.given.ou.any)


if __name__ == '__main__':
    run()

from . import doit
from . import split

# created on 2019-02-23
