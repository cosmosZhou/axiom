from util import *


@apply
def apply(self):
    expr, (i,_a, a1) = self.of(Cap)
    a = a1 - 1
    assert _a == -a
    return Equal(self, Cap[i:-a:a + 1](expr._subs(i, -i)), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra
    i = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True, given=False)
    f = Function(etype=dtype.real)
    Eq << apply(Cap[i:-n:n + 1](f(i)))

    Eq << Eq[0].subs(n, 0)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Sets.Eq.to.Eq.Intersect.apply(Eq[0], f(n + 1))

    Eq << Sets.Eq.to.Eq.Intersect.apply(Eq[-1], f(-n - 1))

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Algebra.Imply.to.Eq.induct.apply(Eq[-1], n=n, start=0)


if __name__ == '__main__':
    run()

# created on 2021-01-23
del oo
from . import oo