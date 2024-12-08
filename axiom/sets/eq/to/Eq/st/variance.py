from util import *


@apply
def apply(eq):
    (a, y), (((S[a], x), (S[x], X)), S[X]) = eq.of(Equal[Indexed, Sum[Indexed] / Card])

    X_ = X | {y}
    return Equal(Sum[x:X_]((a[x] - (Sum[x:X_](a[x])) / (Card(X_))) ** 2),
                 Sum[x:X]((a[x] - (Sum[x:X](a[x])) / Card(X)) ** 2))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    y = Symbol(integer=True, given=True)
    x = Symbol(integer=True)
    a = Symbol(real=True, shape=(oo,), given=True)
    X = Symbol(etype=dtype.integer, finiteset=True, given=True)
    Eq << apply(Equal(a[y], Sum[x:X](a[x]) / Card(X)))

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[1], cond=Element(y, X))

    Eq << Element(y, X).this.apply(Sets.In.to.Eq.Union)

    Eq <<= Eq[-1] & Eq[-3]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Cond.of.And.subs)

    Eq << Algebra.Cond.to.Imply.apply(Eq[0], cond=Eq[3].lhs)

    Eq << Algebra.Imply_And.to.Imply.And.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Sets.Eq.NotIn.to.Eq.st.variance)





if __name__ == '__main__':
    run()
# created on 2021-04-03
# updated on 2023-08-26
