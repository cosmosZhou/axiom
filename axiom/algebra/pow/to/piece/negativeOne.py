from util import *


@apply
def apply(self):
    n = self.of((-1) ** Expr)
    assert n.is_integer
    return Equal(self, Piecewise((1, Equal(n % 2, 0)), (-1, True)))


@prove
def prove(Eq):
    from axiom import algebra, sets

    n = Symbol(integer=True)
    Eq << apply((-1) ** n)

    Eq << algebra.cond_piece.given.ou.apply(Eq[0])

    Eq << Eq[1].this.find(Equal & ~Equal).apply(algebra.is_even.to.eq)

    Eq << Eq[-1].this.find(Unequal).apply(algebra.ne_zero.to.is_odd)

    Eq << Eq[-1].this.find(Equal & ~Equal).apply(algebra.is_odd.to.eq)

    Eq << sets.imply.el.pow.apply((-1) ** n)

    Eq << sets.el_finiteset.imply.ou.eq.apply(Eq[-1])




if __name__ == '__main__':
    run()

# created on 2020-03-01
# updated on 2023-04-30
