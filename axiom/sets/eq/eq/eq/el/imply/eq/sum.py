from util import *


@apply
def apply(eq_cup, eq_cup_complement, eq, contains, sgm):
    if contains.is_Equal:
        eq, contains = contains, eq

    ((a, i), (S[i], S[0], n)), X = eq_cup.of(Equal[Cup[FiniteSet[Indexed]]])
    ((b, k), (S[k], S[0], S[n - 1])), X_complement = eq_cup_complement.of(Equal[Cup[FiniteSet[Indexed]]])
    S[X], y = X_complement.of(Complement[Basic, FiniteSet])

    (S[a], i), S[y] = eq.of(Equal[Indexed])

    faj, (j, (S[n], S[i])) = sgm.of(Sum[Tuple[Complement[Range[0], FiniteSet]]])

    S[X] = n.of(Card)

    S[i], S[n] = contains.of(Element[Range[0]])

    return Equal(sgm, Sum[k:n - 1](faj._subs(a[j], b[k])))


@prove
def prove(Eq):
    from axiom import sets, algebra

    i = Symbol(integer=True, given=True)
    j = Symbol(integer=True)
    X = Symbol(etype=dtype.real, finiteset=True)
    x, y = Symbol(real=True)
    a, b = Symbol(real=True, shape=(oo,))
    f = Function(real=True)
    n = Card(X)
    Eq << apply(Equal(X, a[:n].cup_finiteset()), Equal(X - {y}, b[:n - 1].cup_finiteset()), Equal(y, a[i]), Element(i, Range(n)), Sum[j:Range(n) - {i}](f(a[j])))

    Eq.contains = sets.eq_cup.imply.el.apply(Eq[1])

    Eq << sets.el.imply.eq.card.complement.apply(Eq.contains)

    Eq << Eq[1].subs(Eq[-1].reversed)

    Eq << sets.eq_cup.imply.eq.sum.apply(Eq[-1], Sum[x:X - {y}](f(x)))

    Eq.eq = Eq[-1].subs(Eq[-3])

    Eq << sets.eq_cup.imply.eq.sum.apply(Eq[0], Sum[x:X](f(x)))

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.split, cond={y})

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq.contains, Eq[-1])

    Eq << Eq[-1].this.apply(algebra.eq.transport, lhs=0)

    Eq << Eq[-1].this.rhs.subs(Eq[2])

    Eq << Eq.eq.subs(Eq[-1])

    Eq << Eq[-1].this.lhs.args[1].apply(algebra.sum.to.add.split, cond={i})

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[3], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-03-24
