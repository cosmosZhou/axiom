from util import *


@apply
def apply(equal, contains):
    a, A = contains.of(Element)
    S[A] = equal.of(Equal[Card, 1])
    return Equal(A, a.set, evaluate=False)


@prove
def prove(Eq):
    from Axiom import Set, Algebra, Logic

    A = Symbol(etype=dtype.integer, given=True)
    a = Symbol(integer=True, given=True)
    Eq << apply(Equal(Card(A), 1), Element(a, A))

    Eq << Set.Any.Eq.One.of.Eq.apply(Eq[0], reverse=True)

    Eq << Algebra.Any.And.of.Cond.Any.apply(Eq[1], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(Logic.Cond.of.Eq.Cond.subs, ret=0)

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.of.Eq.Eq.subs, reverse=True)




if __name__ == '__main__':
    run()
# created on 2021-03-15
# updated on 2023-05-20
