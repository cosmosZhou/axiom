from util import *


@apply
def apply(equal, contains):
    a, A = contains.of(Element)
    S[A] = equal.of(Equal[Card, 1])
    return Equal(A, a.set, evaluate=False)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    A = Symbol(etype=dtype.integer, given=True)
    a = Symbol(integer=True, given=True)
    Eq << apply(Equal(Card(A), 1), Element(a, A))

    Eq << Sets.Eq.to.Any.Eq.One.apply(Eq[0], reverse=True)

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[1], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Cond.to.Cond.subs, ret=0)

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Eq.to.Eq.subs, reverse=True)




if __name__ == '__main__':
    run()
# created on 2021-03-15
# updated on 2023-05-20
