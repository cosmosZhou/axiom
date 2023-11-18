from util import *


@apply
def apply(self):
    c, (xi, (i, S[0], n)) = self.of(Element[Cup[FiniteSet]])
    return c >= ReducedMin(Lamda[i:n](xi).simplify())


@prove
def prove(Eq):
    from axiom import algebra, sets

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(oo,))
    c = Symbol(real=True)
    Eq << apply(Element(c, x[:n].cup_finiteset()))

    Eq << Eq[1].this.rhs.apply(algebra.reducedMin.to.minima)

    Eq << algebra.imply.all.ge_minima.apply(Eq[-1].rhs)

    Eq << sets.el_cup.imply.any_el.apply(Eq[0])

    Eq << algebra.all.any.imply.any.et.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.expr.apply(algebra.eq.ge.imply.ge.transit)

    


if __name__ == '__main__':
    run()
# created on 2023-11-12
