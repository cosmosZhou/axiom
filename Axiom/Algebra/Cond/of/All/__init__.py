from util import *


@apply
def apply(given, var=None):
    if var is None:
        var = given.wrt
    from Axiom.Algebra.Cond.to.All import all
    return all(given, var)


@prove
def prove(Eq):
    from Axiom import Algebra

    e = Symbol(positive=True)
    f = Function(shape=(), integer=True)
    Eq << apply(f(e) > 0)

    Eq << Algebra.All.to.Or.apply(Eq[1])

    Eq << Eq[-1].subs(Eq[1].variable, e)


if __name__ == '__main__':
    run()

# created on 2019-03-15
from . import domain_defined
