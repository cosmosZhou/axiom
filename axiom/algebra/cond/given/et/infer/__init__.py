from util import *


@apply
def apply(given, *, cond=None):
    assert cond.is_bool
    return Infer(cond, given), cond


@prove
def prove(Eq):
    from axiom import algebra

    p = Symbol(bool=True)
    f = Function(integer=True, shape=())
    Eq << apply(f(e) > 0, cond=p)

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[2], Eq[1])

    


if __name__ == '__main__':
    run()
# created on 2023-04-18


from . import split