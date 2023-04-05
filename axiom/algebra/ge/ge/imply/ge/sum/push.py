from util import *


@apply
def apply(*imply):
    from axiom.algebra.eq.eq.imply.eq.sum.push import absorb_back
    return absorb_back(Sum, GreaterEqual, *imply)


@prove
def prove(Eq):
    from axiom import algebra
    k, a = Symbol(integer=True)
    b = Symbol(domain=Range(a + 1, oo))
    g, f = Function(integer=True)

    Eq << apply((g(b) >= f(b)), Sum[k:a:b](g(k)) >= Sum[k:a:b](f(k)))

    Eq << algebra.ge.ge.imply.ge.add.apply(Eq[0], Eq[1])

    Eq << Eq[2].this.lhs.apply(algebra.sum.to.add.split, cond={b})

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add.split, cond={b})


if __name__ == '__main__':
    run()

# created on 2019-01-12
