from util import *


@apply
def apply(self):
    expr, (i, *ab) = self.of(Any)
    from Axiom.Algebra.All.of.All.limits.Neg import negate
    return Any(expr._subs(i, -i), negate(i, *ab))


@prove
def prove(Eq):
    from Axiom import Algebra, Set

    i, a, b = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Any[i:a:b](f(i) >= 0))

    Eq << Algebra.Any.And.of.Any.limits.unleash.apply(Eq[0], simplify=False)

    Eq << Algebra.Any.of.Any.limits.Neg.Infty.apply(Eq[-1])

    Eq << Eq[-1].this.find(Element).apply(Set.Neg.In.IccNegS.of.Mem_Icc)


if __name__ == '__main__':
    run()

# created on 2019-02-13


from . import Infty
