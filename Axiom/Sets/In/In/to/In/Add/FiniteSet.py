from util import *


@apply
def apply(contains1, contains2):
    x0, S0 = contains1.of(Element)
    x1, S1 = contains2.of(Element)

    S0 = S0.of(FiniteSet)
    S1 = S1.of(FiniteSet)
    S = {a + b for a in S0 for b in S1}


    return Element(x0 + x1, S)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x0, x1, a, b, c, d, e = Symbol(integer=True)
    Eq << apply(Element(x0, {a, b, c}), Element(x1, {d, e}))

    Eq << Sets.In_FiniteSet.to.Or.Eq.apply(Eq[0])

    Eq << Sets.In_FiniteSet.to.Or.Eq.apply(Eq[1])

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.apply(Algebra.And.to.Or, 1, simplify=None)

    Eq << Eq[-1].this.find(And).apply(Algebra.And.to.Or, simplify=None)

    Eq << Eq[-1].this.args[0].apply(Algebra.Eq.Eq.to.Eq.Add)

    Eq << Eq[-1].this.args[1].apply(Algebra.Eq.Eq.to.Eq.Add)

    Eq << Eq[-1].this.find(And).apply(Algebra.And.to.Or, simplify=None)

    Eq << Eq[-1].this.args[2].apply(Algebra.Eq.Eq.to.Eq.Add)

    Eq << Eq[-1].this.args[3].apply(Algebra.Eq.Eq.to.Eq.Add)

    Eq << Eq[-1].this.find(And).apply(Algebra.And.to.Or, simplify=None)

    Eq << Eq[-1].this.args[4].apply(Algebra.Eq.Eq.to.Eq.Add)

    Eq << Eq[-1].this.args[5].apply(Algebra.Eq.Eq.to.Eq.Add)

    Eq << Sets.In.of.Or.split.FiniteSet.apply(Eq[2])




if __name__ == '__main__':
    run()
# created on 2018-11-18
# updated on 2023-05-20
-20
