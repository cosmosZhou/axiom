from util import *


@apply
def apply(le, contains, notcontains):
    y_, Y = contains.of(Element)
    S[y_], X = notcontains.of(NotElement)

    ((a, S[y_]), (((S[a], x), (S[x], S[X])), S[X])), ((S[a], S[y_]), (((S[a], y), (S[y], Y)), S[Y]))= le.of(Abs[Indexed - Sum[Indexed] / Card] <= Abs[Indexed - Sum[Indexed] / Card])

    X_ = X | {y_}
    Y_ = Y - {y_}
    return LessEqual(Sum[x:X_]((a[x] - (Sum[x:X_](a[x])) / (Card(X) + 1)) ** 2) + Sum[y:Y_]((a[y] - Sum[y:Y_](a[y]) / (Card(Y) - 1)) ** 2),
                     Sum[x:X]((a[x] - (Sum[x:X](a[x])) / Card(X)) ** 2) + Sum[y:Y]((a[y] - Sum[y:Y](a[y]) / Card(Y)) ** 2))


@prove
def prove(Eq):
    from Axiom import Algebra, Set, Logic

    y_quote = Symbol(integer=True, given=True)
    x, y = Symbol(integer=True)
    a = Symbol(real=True, shape=(oo,), given=True)
    X, Y = Symbol(etype=dtype.integer, finiteset=True, given=True)
    Eq << apply(abs(a[y_quote] - Sum[x:X](a[x]) / Card(X)) <= abs(a[y_quote] - Sum[y:Y](a[y]) / Card(Y)), Element(y_quote, Y), NotElement(y_quote, X))

    Eq.eq, Eq.ne = Logic.Cond.given.And.Imp.split.apply(Eq[-1], cond=Equal(Card(Y), 1))

    Eq.suffice_et = Logic.Imp.And.of.Cond.apply(Eq[1], cond=Eq.eq.lhs)

    Eq << Eq.suffice_et.this.rhs.apply(Set.Eq_EmptySet.of.Eq.Mem)

    Eq <<= Eq.eq & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Cond.given.And.subs)

    Eq << Logic.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq.suffice_eq = Eq.suffice_et.this.rhs.apply(Set.EqFinset.of.Eq.Mem)

    Eq <<= Eq.suffice_eq & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Cond.given.And.subs)

    Eq << Logic.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Le.given.Eq)

    Eq << Logic.Imp.of.Cond.apply(Eq[0], cond=Eq[-1].lhs)

    Eq <<= Eq[-1] & Eq.suffice_eq

    Eq << Eq[-1].this.rhs.apply(Logic.Cond.of.Eq.Cond.subs)

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq_0.of.Abs.le.Zero)

    Eq << Logic.Imp.of.Cond.apply(Eq[2], cond=Eq[-1].lhs)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Set.EqSumS_SquareSub_DivSum__Card.of.Eq_DivSum__Card.NotMem)

    Eq << Set.EqCard.of.NotMem.apply(Eq[2])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Set.GeCard.of.Mem.apply(Eq[1])

    Eq << Logic.Imp.And.of.Cond.apply(Eq[-1], cond=Eq.ne.lhs)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ge.of.Gt.strengthen)

    Eq << Logic.Imp.of.Cond.apply(Eq[0] & Eq[1] & Eq[2], cond=Eq.ne.lhs)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Set.LeAddSSumS_SquareSub_Sum.of.Le.Ge.Mem.NotMem)





if __name__ == '__main__':
    run()
# created on 2021-03-25
# updated on 2023-08-26
