from util import *


@apply
def apply(n, k, s0=None, B=None):
    if s0 is None:
        x = Symbol(shape=(oo,), etype=dtype.integer, finiteset=True)
        s0 = Symbol(Cup[x[:k]:Stirling.conditionset(n, k, x)](x[:k].cup_finiteset().set))
    if B is None:
        e = Symbol(**s0.etype.dict)
        assert e.is_extended_real
        B = Symbol(Cup[e:s0]({e | {n.set}}))

        assert B.definition.variable.is_extended_real
    return Equal(Card(s0), Card(B))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    n, k = Symbol(integer=True, positive=True, given=True)
    Eq << apply(n, k)

    s0 = Eq[0].lhs
    s0_quote = Symbol('s_0_quote', conditionset(Eq[0].rhs.variable, Eq[0].rhs.limits[0][1]))
    Eq << s0_quote.this.definition

    Eq.s0_definition = imageset(Eq[0].rhs.variable, Eq[0].rhs.expr.arg, s0_quote).this.subs(Eq[-1]).subs(Eq[0].reversed).reversed

    e = Symbol(etype=dtype.integer.set)
    Eq << Sets.All_And.baseset.apply(s0_quote)

    Eq.x_union_s0, *_ = Algebra.All_And.to.And.All.apply(Eq[-1], slice(1, None, 2))

    i = Symbol(integer=True)
    x = Eq[0].rhs.variable.base
    j = Symbol(domain=Range(k + 1))
    B = Eq[1].lhs
    Eq.plausible_notcontains = All(NotElement({n}, e), (e, s0), plausible=True)

    Eq << Eq.plausible_notcontains.this.limits[0][1].subs(Eq.s0_definition)

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.expr.apply(Sets.In_Cup.to.Any_In)

    Eq << Algebra.All.Any.to.Any.And.apply(Eq.x_union_s0, Eq[-1].reversed, simplify=None)

    Eq << Eq[-1].this.expr.apply(Sets.Eq.Eq.to.Eq.Union)

    Eq << Eq[-1].this().expr.lhs.simplify()

    Eq << Algebra.All_Eq.Any.to.Any.subs.apply(Eq.x_union_s0, Eq[-1])

    Eq << Eq.plausible_notcontains.this.expr.apply(Sets.NotIn.to.Eq_EmptySet.Intersect)

    Eq.all_s0_equality = Eq[-1].this.expr.apply(Sets.Intersect_Eq_EmptySet.to.Eq.Complement)

    x_hat = Symbol(r"\hat{x}", Lamda[i](Piecewise((x[i] - {n} , Equal(i, j)), (x[i], True))))
    Eq.x_hat_definition = x_hat[i].this.definition

    Eq << Algebra.Cond_Piece.to.Or.apply(Eq.x_hat_definition)

    Eq.B_assertion = Sets.All_Any_Eq.split.Imageset.apply(B)

    Eq << Eq.B_assertion.this.expr.expr.apply(Sets.Eq.to.Eq.Complement, {n.set})

    Eq << Algebra.Cond.All.to.All.And.apply(Eq.all_s0_equality, Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(Algebra.All.Any.to.Any.And)

    Eq.all_B_contains = Eq[-1].this.expr.expr.apply(Algebra.Eq.Eq.to.Eq.subs, swap=True).limits_subs(Eq[-1].variable, Eq.all_s0_equality.variable)

    Eq.all_s0_contains = Sets.All_In.split.Imageset.apply(B)

    Eq << Eq.B_assertion.this.expr.expr.apply(Sets.Eq.to.Eq.Intersect, {n.set})

    Eq << Algebra.And.to.And.apply(Eq[-1])

    Eq << Eq[-1].limits_subs(Eq.B_assertion.variable, Eq.B_assertion.expr.variable)

    Eq.all_B_equality = Eq[-1].this.expr.apply(Sets.Eq.to.Eq.Union, Eq[-1].variable)

    Eq << Sets.All_In.All_In.All_Eq.All_Eq.to.Eq.apply(Eq.all_s0_contains, Eq.all_B_contains, Eq.all_s0_equality, Eq.all_B_equality)





if __name__ == '__main__':
    run()

# created on 2020-08-14
# updated on 2023-05-20
