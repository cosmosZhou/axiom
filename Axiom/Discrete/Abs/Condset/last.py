from util import *


@apply
def apply(n, P_quote=None):
    if P_quote is None:
        x = Symbol(shape=(oo,), integer=True, nonnegative=True)
        P_quote = Symbol(conditionset(x[:n + 1], Equal(x[:n].cup_finiteset(), Range(n)) & Equal(x[n], n)))
    else:
        x = P_quote.definition.variable.base

    P = Symbol(conditionset(x[:n], Equal(x[:n].cup_finiteset(), Range(n))))
    return Equal(Card(P), Card(P_quote))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    n = Symbol(integer=True, positive=True)
    Eq << apply(n)

    x = Eq[0].rhs.variable.base
    P = Eq[0].lhs
    P_quote = Eq[1].lhs
    i = Symbol(integer=True)
    x_quote = Symbol("x'", Lamda[i:n + 1](Piecewise((n, Equal(i, n)), (x[i], True))))
    Eq.x_quote_definition = x_quote.this.definition

    Eq << Eq.x_quote_definition[:n]

    Eq.mapping = Eq[-1].this.rhs().expr.simplify()

    Eq << Eq.x_quote_definition[i]

    Eq << Sets.Eq.to.Eq.Cup.FiniteSet.apply(Eq[-1], (i, 0, n))

    Eq.x_quote_n_definition = Eq[-2].subs(i, n)

    Eq << Sets.All_Eq_.CupFiniteSet.Range.apply(P)

    Eq << Algebra.All_Eq.Cond.to.All.subs.apply(Eq[-1], Eq[-2])

    Eq.P2P_quote = All[x[:n]:P](Element(x_quote, P_quote), plausible=True)

    Eq << Eq.P2P_quote.this.expr.rhs.definition

    Eq << Algebra.And.of.And.apply(Eq[-1])

    Eq << Sets.All_Eq_.CupFiniteSet.Range.apply(P_quote)

    Eq << Algebra.All_And.to.And.All.apply(Eq[-1])

    Eq << Algebra.Cond.All.to.All.And.apply(Eq.x_quote_n_definition, Eq[-2], simplify=False)

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Eq.to.Eq.trans, reverse=True)

    Eq.mapping_quote = All[x[:n + 1]:P_quote](Equal(x_quote, x[:n + 1]), plausible=True)

    Eq << Eq.mapping_quote.this.expr.apply(Algebra.Eq.of.And.Eq.Block)

    Eq << Algebra.All_And.of.And.All.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.mapping)

    Eq << All[x[:n + 1]:P_quote](Element(x[:n], P), plausible=True)

    Eq << Eq[-1].this.expr.rhs.definition

    Eq << Sets.All_In.All_In.All_Eq.All_Eq.to.Eq.apply(Eq[-1], Eq.P2P_quote, Eq.mapping_quote, Eq.mapping)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2020-08-01
