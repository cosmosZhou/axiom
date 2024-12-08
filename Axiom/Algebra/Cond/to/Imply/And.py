from util import *


@apply(simplify=None)
def apply(given, *, cond=None):
    assert cond.is_bool
    return Imply(cond, given & cond, evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra

    e = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(f(e) > 0, cond=e > 0)

    Eq << Eq[-1].apply(Algebra.Imply.of.Or)

    Eq << Algebra.Or.of.And.apply(Eq[-1])

    Eq << Algebra.Or.of.Cond.apply(Eq[-1], index=0)




if __name__ == '__main__':
    run()
# created on 2018-08-30
# updated on 2023-05-20
