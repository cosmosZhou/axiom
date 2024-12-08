from util import *


@apply
def apply(n, P_quote=None):
    from Axiom.Discrete.All_And.mapping.Qu2v import predefined_symbols
    Q, w, x = predefined_symbols(n)
    if P_quote is None:
        P_quote = Symbol("P'", conditionset(x[:n + 1], Equal(x[:n].cup_finiteset(), Range(n)) & Equal(x[n], n)))

    return Equal(Q[n], P_quote)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra, Discrete

    n = Symbol(integer=True, positive=True)
    Eq << apply(n)

    Eq << Sets.All_Eq_.CupFiniteSet.Range.apply(Eq[-1].lhs)

    Eq << Algebra.All_And.to.And.All.apply(Eq[-1])

    Eq << Eq[-3].this.expr.apply(Discrete.Eq.Eq.to.Eq.permutation.pop.Interval)

    Eq.all_P_quote = Eq[-1] & Eq[-3]

    Eq << Sets.All_Eq_.CupFiniteSet.Range.apply(Eq[1].lhs)

    Eq << Algebra.All_And.to.And.All.apply(Eq[-1])

    Eq << Eq[-3].this.expr.apply(Discrete.Eq.Eq.to.Eq.permutation.push)

    Eq <<= Eq[-1] & Eq[-3]

    Eq << Sets.All.All.to.Eq.apply(Eq.all_P_quote, Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-07-09
