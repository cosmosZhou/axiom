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
    from axiom import algebra, sets

    y_quote = Symbol(integer=True, given=True)
    x, y = Symbol(integer=True)
    a = Symbol(real=True, shape=(oo,), given=True)
    X, Y = Symbol(etype=dtype.integer, finiteset=True, given=True)
    Eq << apply(abs(a[y_quote] - Sum[x:X](a[x]) / Card(X)) <= abs(a[y_quote] - Sum[y:Y](a[y]) / Card(Y)), Element(y_quote, Y), NotElement(y_quote, X))

    Eq.eq, Eq.ne = algebra.cond.given.et.infer.split.apply(Eq[-1], cond=Equal(Card(Y), 1))

    Eq.suffice_et = algebra.cond.imply.infer.et.apply(Eq[1], cond=Eq.eq.lhs)

    Eq << Eq.suffice_et.this.rhs.apply(sets.eq.el.imply.is_empty)

    Eq <<= Eq.eq & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(algebra.eq.cond.given.et.subs)

    Eq << algebra.infer.given.et.infer.apply(Eq[-1])

    Eq.suffice_eq = Eq.suffice_et.this.rhs.apply(sets.eq.el.imply.eq.finiteset)

    Eq <<= Eq.suffice_eq & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(algebra.eq.cond.given.et.subs)

    Eq << algebra.infer.given.et.infer.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.le.given.eq)

    Eq << algebra.cond.imply.infer.apply(Eq[0], cond=Eq[-1].lhs)

    Eq <<= Eq[-1] & Eq.suffice_eq

    Eq << Eq[-1].this.rhs.apply(algebra.eq.cond.imply.cond.subs)

    Eq << Eq[-1].this.rhs.apply(algebra.abs_le_zero.imply.is_zero)

    Eq << algebra.cond.imply.infer.apply(Eq[2], cond=Eq[-1].lhs)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(sets.eq.notin.imply.eq.st.variance)

    Eq << sets.notin.imply.eq.card.apply(Eq[2])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << sets.el.imply.ge.card.apply(Eq[1])

    Eq << algebra.cond.imply.infer.et.apply(Eq[-1], cond=Eq.ne.lhs)

    Eq << Eq[-1].this.rhs.apply(algebra.gt.imply.ge.strengthen)

    Eq << algebra.cond.imply.infer.apply(Eq[0] & Eq[1] & Eq[2], cond=Eq.ne.lhs)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(sets.le.ge.el.notin.imply.le.st.variance)

    
    


if __name__ == '__main__':
    run()
# created on 2021-03-25
# updated on 2023-08-26
