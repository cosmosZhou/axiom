from util import *


@apply
def apply(given, wrt=None):
    assert given._has(wrt)
    x = given.generate_var(**wrt.type.dict)
    return Exists[x:wrt.domain](given._subs(wrt, x) & Equal(x, wrt))


@prove
def prove(Eq):
    from Axiom import Set, Algebra
    n = Symbol(integer=True, positive=True, given=True)
    e = Symbol(domain=Range(n), given=True)
    f = Function(integer=True, shape=())
    Eq << apply(f(e) > 0, wrt=e)

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.find(Unequal).apply(Set.NotMem.of.Ne)

    Eq << Eq[-1].apply(Algebra.All.of.All_Or.limits.absorb, index=1)

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

# created on 2019-02-26
del Any
from . import Any
