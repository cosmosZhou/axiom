from util import *


@apply
def apply(self):
    expr, (i, *ab) = self.of(Any)
    from Axiom.Algebra.All.to.All.limits.Neg import negate
    return Any(expr._subs(i, -i), negate(i, *ab))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    i, a, b = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Any[i:a:b](f(i) >= 0))

    Eq << Algebra.Any.to.Any.And.limits.unleash.apply(Eq[0], simplify=False)

    Eq << Algebra.Any.to.Any.limits.Neg.oo.apply(Eq[-1])

    Eq << Eq[-1].this.find(Element).apply(Sets.In.to.In.Neg)


if __name__ == '__main__':
    run()

# created on 2019-02-13

del oo
from . import oo
