from util import *


@apply
def apply(given, *, cond=None):
    assert cond.is_bool

    return Or(cond, given), Or(cond.invert(), given)


@prove
def prove(Eq):
    from axiom import algebra

    e = Symbol(integer=True)
    f = Function(integer=True, shape=())
    Eq << apply(f(e) > 0, cond=e > 0)

    Eq << algebra.ou.given.cond.apply(Eq[-2], index=1)

    Eq << algebra.ou.given.cond.apply(Eq[-1], index=0)

    


if __name__ == '__main__':
    run()

# created on 2018-01-03
# updated on 2023-05-20
