from util import *


@apply
def apply(self, A):
    B = self.of(Card)

    return Equal(self, Card(B - A) + Card(A & B))


@prove
def prove(Eq):
    from Axiom import Sets

    A = Symbol(etype=dtype.integer)
    B = Symbol(etype=dtype.integer)
    Eq << apply(Card(B), A)

    C = Symbol(B - A)
    D = Symbol(B & A)
    Eq.C_def = C.this.definition

    Eq.D_def = D.this.definition

    Eq << Sets.Eq.Eq.to.Eq.Union.apply(Eq.C_def, Eq.D_def)

    Eq << Sets.Eq.to.Eq.Card.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Sets.Card.eq.Add)

    Eq << Eq[-1].subs(Eq.C_def, Eq.D_def).reversed












if __name__ == '__main__':
    run()
# created on 2023-06-01
