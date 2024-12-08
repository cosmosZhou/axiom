from util import *


@apply
def apply(*imply):
    from Axiom.Algebra.Eq.Eq.to.Eq.Sum.push import absorb_back
    return absorb_back(Sum, Less, *imply)


@prove
def prove(Eq):
    from Axiom import Algebra
    k, a = Symbol(integer=True)
    b = Symbol(domain=Range(a + 1, oo))
    g, f = Function(integer=True)

    Eq << apply((g(b) < f(b)), Sum[k:a:b](g(k)) < Sum[k:a:b](f(k)))

    Eq << Algebra.Lt.Lt.to.Lt.Add.apply(Eq[0], Eq[1])

    Eq << Eq[2].this.lhs.apply(Algebra.Sum.eq.Add.split, cond={b})

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Add.split, cond={b})


if __name__ == '__main__':
    run()

# created on 2019-09-30
