from util import *


@apply
def apply(*imply):
    from Axiom.Algebra.Eq.Eq.to.Eq.Sum.push import absorb_back
    return absorb_back(Product, Less, *imply, criteria=lambda cond: cond.lhs > 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    k, a = Symbol(integer=True)
    b = Symbol(domain=Range(a + 1, oo))
    g = Function(integer=True, positive=True)
    f = Function(integer=True)
    Eq << apply((g(b) < f(b)), Product[k:a:b](g(k)) < Product[k:a:b](f(k)))

    Eq << Algebra.Lt.Lt.to.Lt.Mul.apply(Eq[0], Eq[1])

    Eq << Eq[2].this.lhs.apply(Algebra.Prod.eq.Mul.split, cond={b})

    Eq << Eq[-1].this.rhs.apply(Algebra.Prod.eq.Mul.split, cond={b})


if __name__ == '__main__':
    run()

# created on 2019-09-29
