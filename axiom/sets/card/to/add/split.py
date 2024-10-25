from util import *


@apply
def apply(self, A):
    B = self.of(Card)

    return Equal(self, Card(B - A) + Card(A & B))


@prove
def prove(Eq):
    from axiom import sets

    A = Symbol(etype=dtype.integer)
    B = Symbol(etype=dtype.integer)
    Eq << apply(Card(B), A)

    C = Symbol(B - A)
    D = Symbol(B & A)
    Eq.C_def = C.this.definition

    Eq.D_def = D.this.definition

    Eq << sets.eq.eq.then.eq.union.apply(Eq.C_def, Eq.D_def)

    Eq << sets.eq.then.eq.card.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(sets.card.to.add)

    Eq << Eq[-1].subs(Eq.C_def, Eq.D_def).reversed












if __name__ == '__main__':
    run()
# created on 2023-06-01
