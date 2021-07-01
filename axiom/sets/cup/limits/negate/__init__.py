from util import *


@apply
def apply(self):
    expr, (i,_a, a1) = self.of(Cup)
    a = a1 - 1
    assert _a == -a
    return Equal(self, Cup[i:-a:a + 1](expr._subs(i, -i)), evaluate=False)


@prove
def prove(Eq):
    from axiom import sets, algebra

    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, nonnegative=True, given=False)
    f = Function.f(etype=dtype.real)
    Eq << apply(Cup[i:-n:n + 1](f(i)))

    Eq << Eq[0].subs(n, 0)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << sets.eq.imply.eq.union.apply(Eq[0], f(n + 1))

    Eq << sets.eq.imply.eq.union.apply(Eq[-1], f(-n - 1))

    Eq << Suffice(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.suffice.imply.eq.induct.apply(Eq[-1], n=n, start=0)


if __name__ == '__main__':
    run()
    
from . import infinity