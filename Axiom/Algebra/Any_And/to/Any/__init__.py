from util import *


@apply
def apply(given, index=0):
    eqs, *limits = given.of(Any[And])
    eq = eqs[index]
    return Any(eq, *limits)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, c = Symbol(real=True)
    a, b = Symbol(real=True, given=True)
    f = Function(shape=(), real=True)
    Eq << apply(Any[x:a:b]((x <= c) & (f(x) >= 1)), index=1)

    Eq << ~Eq[-1]

    Eq << Algebra.All.Any.to.Any.And.apply(Eq[-1], Eq[0])





if __name__ == '__main__':
    run()

# created on 2018-04-09
# updated on 2023-07-02

from . import limits_delete
from . import limits_absorb
