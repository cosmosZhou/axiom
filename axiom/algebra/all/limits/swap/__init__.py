from util import *


@apply
def apply(self, i=0, j=1):
    from axiom.algebra.sum.limits.swap import rewrite
    return rewrite(All, self, i, j)


@prove
def prove(Eq):
    from axiom import algebra

    a, b, c, d = Symbol(real=True, positive=True)
    x, y = Symbol(real=True)
    f, g = Function(bool=True)
    Eq << apply(All[x:a:b, y:c:d](f(x) & g(x, y)))

    Eq << Eq[0].this.lhs.apply(algebra.all.to.ou)

    Eq << Eq[-1].this.rhs.apply(algebra.all.to.ou)


if __name__ == '__main__':
    run()
# created on 2023-07-02


from . import intlimit
