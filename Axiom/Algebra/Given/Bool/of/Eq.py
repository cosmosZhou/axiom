from util import *



@apply
def apply(given):
    p, q = given.of(Imply)

    return Equal(Bool(p), Bool(p) * Bool(q))


@prove
def prove(Eq):
    from Axiom import Algebra, Logic
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))

    Eq << apply(Imply(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))

    Eq << Imply(Equal(Bool(Eq[0].lhs), 1), Equal(Bool(Eq[0].rhs), 1), plausible=True)

    Eq << Eq[-1].this.lhs.lhs.apply(Logic.Bool.eq.Ite)

    Eq << Eq[-1].this.rhs.lhs.apply(Logic.Bool.eq.Ite)

    Eq << Eq[-2].apply(Logic.Or.of.ImpNot)

    Eq << Eq[-1].this.args[1].apply(Logic.Bool.eq.Zero.of.Bool.ne.One)

    Eq << Algebra.Mul.eq.Zero.of.OrEqS.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.expand()


if __name__ == '__main__':
    run()
# created on 2019-04-03
