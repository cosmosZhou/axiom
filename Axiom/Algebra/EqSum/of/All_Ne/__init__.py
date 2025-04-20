from util import *


@apply
def apply(given, sgm):
    (y, xi), (i, S[0], n) = given.of(All[Unequal])
    ft, (t, s) = sgm.of(Sum)
    xj, (j, S[0], S[n]) = s.of(Cup[FiniteSet])
    assert xj._subs(j, i) == xi

    return Equal(sgm, Sum[t:s | {y}](ft) - ft._subs(t, y), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    x = Symbol(complex=True, shape=(oo,))
    y, t = Symbol(complex=True)
    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Function(complex=True)
    Eq << apply(All[i:n](Unequal(y, x[i])), Sum[t:x[:n].cup_finiteset()](f(t)))

    Eq << Set.Inter_Eq_EmptySet.of.All_Ne.apply(Eq[0])

    Eq << Set.EqSum.of.Inter_Eq_EmptySet.apply(Eq[-1], Eq[1].rhs.args[1])

    Eq << Eq[-1].this.apply(Algebra.Eq.transport, rhs=0)
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-02-04


from . import double_limits
