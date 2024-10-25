from util import *


@apply
def apply(S):
    assert S.is_set

    x = S.element_symbol()
    y = S.element_symbol({x})
    return LessEqual(Card(S), 1) | Any[x:S, y:S](Unequal(x, y))


@prove
def prove(Eq):
    from axiom import algebra, sets

    S = Symbol(etype=dtype.real)
    Eq << apply(S)

    Eq << Eq[-1].apply(algebra.cond.of.et.all, cond=Card(S) >= 2)

    Eq.ge, Eq.lt = algebra.et.of.et.apply(Eq[-1])

    Eq << algebra.then.all.limits_assert.apply(Eq.lt.limits)

    Eq << Eq[-1].this.expr.apply(algebra.lt.then.le.strengthen)

    Eq << algebra.all_ou.of.all.apply(Eq.lt)

    Eq << algebra.then.all.limits_assert.apply(Eq.ge.limits)

    Eq << Eq[-1].this.expr.apply(sets.ge.then.any.ne)




if __name__ == '__main__':
    run()

# created on 2020-07-16
# updated on 2023-05-20
