from util import *


@apply
def apply(self):
    c, (xi, (i, S[0], n)) = self.of(Element[Cup[FiniteSet]])
    return c <= ReducedMax(Lamda[i:n](xi).simplify())


@prove
def prove(Eq):
    from axiom import algebra, sets

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(oo,))
    c = Symbol(real=True)
    Eq << apply(Element(c, x[:n].cup_finiteset()))

    Eq << Eq[1].this.rhs.apply(algebra.reducedMax.to.maxima)

    Eq << algebra.then.all.le_maxima.apply(Eq[-1].rhs)

    Eq << sets.el_cup.then.any_el.apply(Eq[0])

    Eq << algebra.all.any.then.any.et.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.expr.apply(algebra.eq.le.then.le.trans)


if __name__ == '__main__':
    run()
# created on 2023-11-12
