from util import *


@apply
def apply(self):
    from axiom.algebra.mul.to.sum import rewrite
    return Equal(self, rewrite(Integral, self))


@prove
def prove(Eq):
    x, y, a, b, c, d = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Integral[x:a:b](f(x)) * y)

    Eq << Eq[-1].this.rhs.simplify()

    


if __name__ == '__main__':
    run()

from . import as_multiple_limits
# created on 2020-06-06
# updated on 2023-03-28
