from util import *


@apply
def apply(given, old, new):
    expr, (n, a, b) = given.of(Any[Tuple])
    assert n.is_integer
    assert old == n
    m = new + n + 1
    return Any[n:m - b:m - a](expr._subs(old, new))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    n, m = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(Any[n:m + 1](f(n) > 0), n, m - n)

    Eq << Algebra.Any.to.Any.And.limits.unleash.apply(Eq[0], simplify=None)

    Eq << Algebra.Any.to.Any.limits.Neg.oo.apply(Eq[-1])

    Eq << Eq[-1].this.find(Element).apply(Sets.In.to.In.Neg)

    Eq << Algebra.Any.to.Any.limits.subs.offset.apply(Eq[-1], -m)


if __name__ == '__main__':
    run()

# created on 2019-02-18
from . import real
