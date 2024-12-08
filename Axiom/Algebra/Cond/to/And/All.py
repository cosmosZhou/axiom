from util import *


@apply
def apply(given, *, cond=None, wrt=None):
    assert cond.is_bool

    if wrt is None:
        wrt = cond.wrt
    if wrt.is_given:
        _eq = cond.invert()
        return Or(cond, given), Or(_eq, given)

    if wrt.is_bounded:
        from Axiom.Algebra.Cond.to.All import all
        given = all(given, wrt)
    else:
        given = All(given, (wrt,))
    assert given.is_ForAll

    from Axiom.Algebra.Sum.eq.Add.split import split
    given = split(All, given, wrt.domain_conditioned(cond))
    lhs, rhs = given.of(And)
    return lhs, rhs


@prove
def prove(Eq):
    from Axiom import Algebra

    e = Symbol(integer=True)
    f = Function(integer=True, shape=())
    Eq << apply(f(e) > 0, cond=e > 0)

    Eq <<= Algebra.All.of.Or.apply(Eq[-2]), Algebra.All.of.Or.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    run()

# created on 2018-04-10
