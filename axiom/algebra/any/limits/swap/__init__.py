from util import *


@apply
def apply(self, i=0, j=1):
    from axiom.algebra.sum.limits.swap import rewrite
    return rewrite(Any, self, i, j)


@prove
def prove(Eq):
    from axiom import algebra

    a, b, c, d = Symbol(real=True, positive=True)
    x, y = Symbol(real=True)
    f, g = Function(bool=True)
    Eq << apply(Any[x:a:b, y:c:d](f(x) & g(x, y)))

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.any.imply.any.limits.swap, simplify=None)

    Eq << Eq[-1].this.rhs.apply(algebra.any.given.any.limits.swap, simplify=None)



if __name__ == '__main__':
    run()
# created on 2023-07-02


from . import intlimit
from . import subs
# updated on 2023-11-12
