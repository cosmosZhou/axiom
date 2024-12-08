from util import *


@apply
def apply(n):
    from Axiom.Discrete.All_And.mapping.Qu2v import predefined_symbols
    Q, w, x = predefined_symbols(n)

    Pn1 = Symbol("P_{n+1}", conditionset(x[:n + 1], Equal(x[:n + 1].cup_finiteset(), Range(n + 1))))

    t = Q.definition.variable
    return Equal(Cup[t](Q[t]), Pn1)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    n = Symbol(integer=True, positive=True)
    Eq << apply(n)

    Q = Eq[0].lhs.base
    t = Q.definition.variable
    Eq << Subset(Eq[0].lhs, Eq[2].rhs, plausible=True)

    Eq.subset_P = Sets.Subset.to.Subset.Cup.lhs.apply(Eq[-1], (t,), simplify=False)

    Eq.subset_Q = Subset(Eq.subset_P.rhs, Eq.subset_P.lhs, plausible=True)

    Eq << Sets.Subset.of.All_In.apply(Eq.subset_Q)

    Eq << Eq[-1].limits_subs(Eq[-1].variable, Eq[0].rhs.variable)

    Eq << Eq[-1].this.expr.apply(Sets.In_Cup.of.Any_In)

    Eq << Eq[-1].this.expr.expr.rhs.definition

    Eq << Algebra.All_And.of.And.All.apply(Eq[-1])

    Eq << Eq[-2].this.limits[0][1].definition

    Eq << Eq[-1].this.limits[0][1].definition

    Eq << Algebra.All.of.Imply.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Sets.Eq.to.In.st.Cup, index=n)

    Eq <<= Eq.subset_P & Eq.subset_Q




if __name__ == '__main__':
    run()
# created on 2020-08-04
# updated on 2023-05-20
