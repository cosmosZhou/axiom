from util import *


@apply
def apply(S):
    assert S.is_set

    x = S.element_symbol()
    y = S.element_symbol({x})
    return LessEqual(Card(S), 1) | Any[x:S, y:S](Unequal(x, y))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    S = Symbol(etype=dtype.real)
    Eq << apply(S)

    Eq << Eq[-1].apply(Algebra.Cond.of.And.All, cond=Card(S) >= 2)

    Eq.ge, Eq.lt = Algebra.And.of.And.apply(Eq[-1])

    Eq << Algebra.All.limits_assert.apply(Eq.lt.limits)

    Eq << Eq[-1].this.expr.apply(Algebra.Lt.to.Le.strengthen)

    Eq << Algebra.All_Or.of.All.apply(Eq.lt)

    Eq << Algebra.All.limits_assert.apply(Eq.ge.limits)

    Eq << Eq[-1].this.expr.apply(Sets.Ge.to.Any.Ne)




if __name__ == '__main__':
    run()

# created on 2020-07-16
# updated on 2023-05-20
