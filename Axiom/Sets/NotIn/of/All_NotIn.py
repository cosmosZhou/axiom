from util import *


@apply
def apply(given):
    e, S = given.of(NotElement)
    expr, *limits = S.of(Cup)
    return All(NotElement(e, expr).simplify(), *limits)


@prove
def prove(Eq):
    from Axiom import Sets

    n = Symbol(integer=True, positive=True, given=True)
    x = Symbol(integer=True, given=True)
    k = Symbol(integer=True)
    A = Symbol(shape=(oo,), etype=dtype.integer, given=True)
    Eq << apply(NotElement(x, Cup[k:n](A[k])))

    Eq << ~Eq[0]

    Eq << Sets.In_Cup.to.Any_In.apply(Eq[-1], simplify=None)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2019-02-02
