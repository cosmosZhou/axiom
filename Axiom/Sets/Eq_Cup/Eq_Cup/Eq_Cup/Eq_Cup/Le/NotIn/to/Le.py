from util import *


@apply
def apply(eq_cup_X, eq_cup_Y, eq_cup_X_union, eq_cup_Y_complement, le, notcontains):
    ((t, y_), (((S[t], x), (S[x], X)), S[X])), ((S[t], S[y_]), (((S[t], y), (S[y], Y)), S[Y]))= le.of(Abs[Indexed - Sum[Indexed] / Card] <= Abs[Indexed - Sum[Indexed] / Card])

    S[y_], S[X] = notcontains.of(NotElement)

    ((a, i), (S[i], S[0], n)), S[X] = eq_cup_X.of(Equal[Cup[FiniteSet[Indexed]]])

    ((a_, i), (S[i], S[0], S[n + 1])), X_union = eq_cup_X_union.of(Equal[Cup[FiniteSet[Indexed]]])

    ((b, i), (S[i], S[0], m)), S[Y] = eq_cup_Y.of(Equal[Cup[FiniteSet[Indexed]]])

    ((b_, i), (S[i], S[0], S[m - 1])), Y_complement = eq_cup_Y_complement.of(Equal[Cup[FiniteSet[Indexed]]])

    if not X_union.is_Union:
        eq_cup_Y, eq_cup_X_union = eq_cup_X_union, eq_cup_Y
        ((S[a_], i), (S[i], S[0], S[n + 1])), S[X_union] = eq_cup_X_union.of(Equal[Cup[FiniteSet[Indexed]]])
        ((S[b], i), (S[i], S[0], S[m])), S[Y] = eq_cup_Y.of(Equal[Cup[FiniteSet[Indexed]]])

    S[y_], S[X] = X_union.of(Union[FiniteSet, Basic])

    S[Y], S[y_] = Y_complement.of(Complement[Basic, FiniteSet])

    X_ = X | {y_}
    Y_ = Y - {y_}

    return LessEqual(Sum[x:X_]((t[x] - (Sum[x:X_](t[x])) / (Card(X) + 1)) ** 2) + Sum[y:Y_]((t[y] - Sum[y:Y_](t[y]) / (Card(Y) - 1)) ** 2),
                     Sum[x:X]((t[x] - (Sum[x:X](t[x])) / Card(X)) ** 2) + Sum[y:Y]((t[y] - Sum[y:Y](t[y]) / Card(Y)) ** 2))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x, y, i = Symbol(integer=True)
    y_quote = Symbol(integer=True, given=True)
    t = Symbol(real=True, shape=(oo,), given=True)
    X, Y = Symbol(etype=dtype.integer, finiteset=True, given=True)
    a, b, a_quote, b_quote = Symbol(shape=(oo,), integer=True)
    Eq << apply(Equal(X, Cup[i:Card(X)]({a[i]})), Equal(Y, Cup[i:Card(Y)]({b[i]})), Equal(X | {y_quote}, Cup[i:Card(X) + 1]({a_quote[i]})), Equal(Y - {y_quote}, Cup[i:Card(Y) - 1]({b_quote[i]})), abs(t[y_quote] - Sum[x:X](t[x]) / Card(X)) <= abs(t[y_quote] - Sum[y:Y](t[y]) / Card(Y)), NotElement(y_quote, X))

    Eq << Sets.Eq_Cup.to.Eq.Sum.apply(Eq[0], Eq[6].rhs.args[0].find(Pow, Sum))

    Eq.given = Eq[4].subs(Eq[-1])

    Eq << Sets.Eq_Cup.to.Eq.Sum.apply(Eq[0], Eq[6].rhs.args[0])

    Eq << Eq[-1].this.rhs.subs(Eq[-2])

    Eq << Sets.Eq_Cup.to.Eq.Sum.apply(Eq[1], Eq[6].rhs.args[1].find(Pow, Sum))

    Eq.given = Eq.given.subs(Eq[-1])

    Eq << Sets.Eq_Cup.to.Eq.Sum.apply(Eq[1], Eq[6].rhs.args[1])

    Eq << Eq[-1].this.rhs.subs(Eq[-2])

    Eq.add_ab = Eq[-4] + Eq[-1]

    Eq.abs_union = Sets.NotIn.to.Eq.Card.apply(Eq[5])

    Eq << Eq[2].subs(Eq.abs_union.reversed)

    Eq << Sets.Eq_Cup.to.Eq.Sum.apply(Eq[-1], Eq[6].lhs.args[0].find(Pow, Sum))

    Eq << Sets.Eq_Cup.to.Eq.Sum.apply(Eq[-2], Eq[6].lhs.args[0])

    Eq << Eq[-1].this.rhs.subs(Eq[-2])

    Eq.eq_X_union = Eq[-1].subs(Eq.abs_union)

    Eq.contains = Sets.Eq_Cup.to.In.apply(Eq[3])

    Eq.abs_complement = Sets.In.to.Eq.Card.Complement.apply(Eq.contains)

    Eq << Eq[3].subs(Eq.abs_complement.reversed)

    Eq << Sets.Eq_Cup.to.Eq.Sum.apply(Eq[-1], Eq[6].lhs.args[1].find(Pow, Sum))

    Eq << Sets.Eq_Cup.to.Eq.Sum.apply(Eq[-2], Eq[6].lhs.args[1])

    Eq << Eq[-1].this.rhs.subs(Eq[-2])

    Eq.eq_Y_complement = Eq[-1].subs(Eq.abs_complement)

    Eq << Sets.Eq_Cup.In.to.Any.Eq.apply(Eq[1], Eq.contains)

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq.given, Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Cond.to.Cond.subs, ret=0)

    Eq << Algebra.Any.to.Any.And.limits.Cond.apply(Eq[-1], 0, simplify=None)

    Eq << Algebra.Any_And.to.Any.limits_absorb.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(Sets.Le_Abs.In.to.Le, simplify=None, ret=1)

    Eq << Eq[-1].subs(Eq.add_ab.reversed)

    Eq << Eq[-1].this.find(Element).apply(Sets.In.to.Eq.Sum, Eq[-1].find(Sum[2]).find(Sum), simplify=None, ret=0)

    Eq << Eq[-1].this.expr.args[:2].apply(Algebra.Eq.Cond.to.Cond.subs, simplify=None)

    Eq << Eq[-1].this.expr.args[1].apply(Sets.In.to.Eq.Sum, Eq[-1].expr.args[0].lhs.args[3])

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Cond.to.Cond.subs, simplify=None)

    Eq << Algebra.Any.to.Any.And.limits.Cond.apply(Eq[-1], 0, simplify=None)

    Eq << Algebra.Any_And.to.Any.limits_absorb.apply(Eq[-1], -1, simplify=None)

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Cond.to.Cond.subs, reverse=True)

    Eq << Sets.Eq_Cup.Eq_Cup.NotIn.to.Eq.Sum.apply(Eq[0], Eq[2], Eq[5], Eq.eq_X_union.rhs.find(Sum))

    Eq << Eq[-2].subs(Eq[-1].reversed)

    j = Eq[-1].expr.lhs.args[1].variable
    Eq << Eq[-1].this.expr.lhs.args[1].limits_subs(j, i, simplify=None)

    Eq << Sets.Eq_Cup.Eq_Cup.NotIn.to.Eq.Sum.apply(Eq[0], Eq[2], Eq[5], Eq.eq_X_union.rhs)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[1] & Eq[3], Eq[-1], simplify=None)

    Eq << Algebra.Any.to.Any.And.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Algebra.Any_And.to.Any.limits_absorb.apply(Eq[-1], -2, simplify=None)

    Eq << Eq[-1].this.expr.apply(Sets.Eq.Eq.Eq.In.to.Eq.Sum, Eq[-1].find(Sum[2]).find(Sum), simplify=None, ret=slice(None))

    Eq << Algebra.Any.to.Any.And.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.args[3:5].apply(Algebra.Eq.Cond.to.Cond.subs, simplify=None)

    Eq << Algebra.Any_And.to.Any.limits_absorb.apply(Eq[-1], -2, simplify=None)

    Eq << Eq[-1].this.expr.apply(Sets.Eq.Eq.Eq.In.to.Eq.Sum, Eq[-1].find(Sum[2]), simplify=None)

    Eq << Algebra.Any.to.Any.And.limits.unleash.apply(Eq[-1], simplify=None)


    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Cond.to.Cond.subs)
    Eq << Eq[-1].subs(Eq.eq_X_union.reversed, Eq.eq_Y_complement.reversed)




if __name__ == '__main__':
    run()
# created on 2021-03-24
# updated on 2023-05-20