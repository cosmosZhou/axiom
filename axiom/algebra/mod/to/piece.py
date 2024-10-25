from util import *


@apply
def apply(self):
    n, S[2] = self.of(Expr % Expr)
    assert n.is_integer
    return Equal(self, Piecewise((0, Equal(n % 2, 0)), (1, True)))


@prove
def prove(Eq):
    from axiom import algebra, sets

    n = Symbol(integer=True)
    Eq << apply(n % 2)

    Eq << algebra.cond_piece.of.ou.apply(Eq[0])

    Eq << sets.ou.of.el.finiteset.apply(Eq[-1])

    Eq << sets.then.el.mod.apply(Eq[-1].lhs)

    Eq << Eq[-1].this.rhs.apply(sets.range.to.finiteset)




if __name__ == '__main__':
    run()
# created on 2022-01-20
# updated on 2023-04-30
