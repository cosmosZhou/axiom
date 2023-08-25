from util import *


@apply
def apply(self, i=0, j=1):
    from axiom.algebra.sum.limits.swap import rewrite
    return rewrite(Any, self, i, j)


@prove(provable=False)
def prove(Eq):
    a, b, c, d = Symbol(real=True, positive=True)
    x, y = Symbol(real=True)
    f, g = Function(bool=True)
    Eq << apply(Any[x:a:b, y:c:d](f(x) & g(x, y)))


if __name__ == '__main__':
    run()
# created on 2023-07-02


from . import intlimit