from util import *


@apply(simplify=None)
def apply(given, *, cond=None):
    assert cond.is_bool
    return Infer(cond, given & cond, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    e = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(f(e) > 0, cond=e > 0)

    Eq << Eq[-1].apply(algebra.infer.of.ou)

    Eq << algebra.ou.of.et.apply(Eq[-1])

    Eq << algebra.ou.of.cond.apply(Eq[-1], index=0)




if __name__ == '__main__':
    run()
# created on 2018-08-30
# updated on 2023-05-20
