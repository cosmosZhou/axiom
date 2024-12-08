from util import *


@apply
def apply(given, sgm):
    e, s = given.of(NotElement)
    fx, (x, _s) = sgm.of(Sum)
    S[e] = _s.of(Union[s, FiniteSet])
    return Equal(Sum[x:s | {e}](fx), Sum[x:s](fx) + fx._subs(x, e))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    S = Symbol(etype=dtype.integer)
    e, x = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(NotElement(e, S), Sum[x:S | {e}](f(x)))

    Eq << Sets.NotIn.to.Eq_EmptySet.Intersect.apply(Eq[0])

    Eq << Eq[1].this.lhs.apply(Algebra.Sum.eq.Add.split, cond={e})

    Eq << Sets.NotIn.to.Eq.Complement.apply(Eq[0])
    Eq << Eq[-2].subs(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-03-17
