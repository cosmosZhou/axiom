from util import *


@apply
def apply(ge, sgm):
    a, b = ge.of(GreaterEqual)
    expr, (k, S[a], S[b]) = sgm.of(Sum)
    return Equal(sgm, 0)


@prove
def prove(Eq):
    from axiom import algebra, sets

    a, b = Symbol(integer=True, given=True)
    n = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(a >= b, Sum[n:a:b](f(n)))

    Eq << Eq[-1].this.lhs.apply(algebra.sum.bool)

    Eq << sets.ge.then.is_empty.range.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-06-03
