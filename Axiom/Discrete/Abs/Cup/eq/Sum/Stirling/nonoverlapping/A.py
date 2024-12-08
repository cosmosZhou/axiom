from util import *


@apply
def apply(n, k, A=None):
    from sympy.functions.combinatorial.numbers import Stirling
    assert k < n
    j = Symbol(domain=Range(k + 1))
    if A is None:
        x = Symbol(shape=(oo,), etype=dtype.integer, finiteset=True)
        i = Symbol(integer=True)
        s1_quote = Symbol("s'_1", Stirling.conditionset(n, k + 1, x))
        x_quote = Symbol("x'", Lamda[i:k + 1](Piecewise(({n} | x[i], Equal(i, j)), (x[i], True))))
        A = Symbol(Lamda[j](Cup[x[:k + 1]:s1_quote]({x_quote.cup_finiteset()})))

    return Equal(Card(Cup[j](A[j])), Sum[j](Card(A[j])))


@prove(proved=False)
def prove(Eq):
    from Axiom import Sets, Algebra, Discrete

    n = Symbol(integer=True, positive=True)
    k = Symbol(domain=Range(1, n))
    Eq << apply(n, k)

    s1_quote = Eq[1].lhs
    Eq.s1_quote_definition = Sets.All_Eq_.CupFiniteSet.Range.apply(s1_quote)

    i = Eq[0].lhs.indices[0]
    Eq.x_abs_positive_s1 = Algebra.All_And.to.All.apply(Eq.s1_quote_definition)

    Eq.x_abs_sum_s1 = Algebra.All_And.to.All.apply(Eq.s1_quote_definition, 1)

    Eq.x_Union_s1 = Algebra.All_And.to.All.apply(Eq.s1_quote_definition, 2)

    j = Symbol(domain=Range(k + 1))
    Eq << Sets.Eq.to.Eq.Cup.apply(Eq[0], (i, 0, k + 1))

    Eq.x_quote_Union = Algebra.All_Eq.Cond.to.All.subs.apply(Eq.x_Union_s1, Eq[-1])

    Eq << Eq[0].apply(Sets.Eq.to.Eq.Card)

    x_quote_abs = Eq[-1]
    Eq << Eq[-1].apply(Algebra.Eq.to.Eq.Sum, (i, 0, k + 1))

    Eq << Sets.CardUnion.le.AddCardS.apply(*Eq[-1].rhs.args[1].arg.args)

    Eq << Algebra.Eq.Le.to.Le.subs.apply(Eq[-2], Eq[-1])

    Eq << Algebra.All_Eq.Cond.to.All.subs.apply(Eq.x_abs_sum_s1, Eq[-1])

    Eq << Eq.x_quote_Union.this.expr.apply(Sets.Eq.to.Eq.Card)

    u = Eq[-1].lhs.arg
    Eq.SqueezeTheorem = Sets.CardCup.le.Sum_Card.apply(u.expr, *u.limits)

    Eq << Algebra.Cond_Piece.to.Or.apply(x_quote_abs)

    Eq << Eq[-1].subs(i, j)

    Eq << Algebra.Cond.to.All.restrict.apply(Eq[-2], (i, Unequal(i, j)))

    Eq << Sets.CardUnion.ge.Card.apply(*Eq[-2].rhs.arg.args[::-1])

    Eq << Eq.x_abs_positive_s1.limits_subs(i, j).this.expr.apply(Algebra.Gt.Ge.to.Gt.trans, Eq[-1])

    Eq <<= Eq[-1] & Eq[-2]

    Eq <<= Eq.x_quote_Union & Eq.SqueezeTheorem & Eq[-1]

    Eq.x_quote_definition = Algebra.Eq.to.Eq.Lamda.apply(Eq[0], (i, 0, k + 1))

    Eq << Eq.x_Union_s1.this.expr.apply(Sets.Eq.then.Eq.intersect, {n})

    Eq.nonoverlapping_s1_quote = Eq[-1].this.expr.apply(Sets.is_empty.then.All_is_empty.intersect)

    Eq.xi_complement_n = Eq.nonoverlapping_s1_quote.this.expr.apply(Sets.Intersect_Eq_EmptySet.to.Eq.Complement, reverse=True)

    A_quote = Symbol(Lamda[j](Eq[2].rhs.expr))
    Eq.A_quote_definition = A_quote.this.definition

    Eq.A_definition_simplified = Eq[2].this.rhs.subs(Eq.A_quote_definition[j].reversed)

    j_quote = Symbol(integer=True)
    Eq.nonoverlapping = All(Equal(A_quote[j_quote] & A_quote[j], A_quote[j].etype.emptySet), *((j_quote, Range(k + 1) - {j}),) + Eq.A_definition_simplified.rhs.limits, plausible=True)

    Eq << ~Eq.nonoverlapping

    Eq << Eq[-1].this.expr.apply(Sets.Intersect_ne_empty.then.Any_In, simplify=None)

    Eq << Eq[-1].this.expr.subs(Eq.A_quote_definition[j])

    Eq << Eq[-1].this.expr.subs(Eq.A_quote_definition[j_quote])

    Eq << Eq[-1].this.expr.rhs.expr.arg.definition

    Eq << Eq[-1].this.expr.apply(Sets.Eq.to.Supset)

    Eq << Eq[-1].this.expr.apply(Sets.supset_Cup.then.All_supset)

    Eq << Eq[-1].this.expr.subs(Eq[-1].expr.variable, Eq[-1].variable)

    Eq << Eq[-1].this.expr.apply(Sets.In_Cup.to.Any_In)

    Eq << Eq[-1].this.expr.subs(Eq.x_quote_definition)

    Eq << Eq[-1].this.expr.apply(Algebra.Cond_Piece.to.Or)

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.expr.apply(Algebra.All_And.of.And.All)


if __name__ == '__main__':
    run()

# created on 2020-08-11
