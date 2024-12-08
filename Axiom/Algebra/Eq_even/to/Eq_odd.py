from util import *


@apply
def apply(given):
    n = given.of(Equal[Expr % 2, 0])
    return Equal((n + 1) % 2, 1)


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True)
    Eq << apply(Equal(n % 2, 0))

    Eq << Eq[1].lhs.this.apply(Algebra.Mod.eq.Sub)

    Eq << Eq[0].this.lhs.apply(Algebra.Mod.eq.Sub).reversed



    Eq << Eq[-2].this.rhs.subs(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-05-30
