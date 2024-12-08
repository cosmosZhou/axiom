from util import *


@apply
def apply(eq_mod, contains):
    (x, m), d = eq_mod.of(Equal[Mod])
    S[x], args = contains.of(Element[FiniteSet])

    deletes = set()
    for a in args:
        if Equal(a % m, d) == False:
            deletes.add(a)
    assert deletes
    s = {*args} - deletes

    return Element(x, s)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(integer=True)
    Eq << apply(Equal(x % 3, 1), Element(x, {-2, -1, 0, 1, 2}))

    Eq << Sets.In_FiniteSet.to.Or.Eq.apply(Eq[1])

    Eq <<= Eq[-1] & Eq[0]

    Eq << Algebra.And.to.Or.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.args[-1].apply(Algebra.Eq.Eq.to.Eq.subs, simplify=None)

    Eq << Eq[-1].this.args[-2].apply(Algebra.Eq.Eq.to.Eq.subs, simplify=None)

    Eq << Eq[-1].this.args[0].apply(Algebra.Eq.Eq.to.Eq.subs)

    Eq << Algebra.And.to.Cond.apply(Eq[-1], 1)

    Eq << Sets.Or_Eq.to.In.FiniteSet.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2018-11-19
# updated on 2023-05-12
