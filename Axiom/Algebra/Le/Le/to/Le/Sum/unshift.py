from util import *


@apply
def apply(*imply):
    from Axiom.Algebra.Eq.Eq.to.Eq.Sum.unshift import absorb_front
    return absorb_front(Sum, LessEqual, *imply)


@prove
def prove(Eq):
    from Axiom import Algebra

    k, a = Symbol(integer=True)
    b = Symbol(domain=Range(a + 1, oo))
    g, f = Function(integer=True)
    Eq << apply((g(a - 1) <= f(a - 1)), Sum[k:a:b](g(k)) <= Sum[k:a:b](f(k)))

    Eq << Algebra.Le.Le.to.Le.Add.apply(Eq[0], Eq[1])

    Eq << Eq[2].this.lhs.apply(Algebra.Sum.eq.Add.split, cond={a - 1})

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Add.split, cond={a - 1})


if __name__ == '__main__':
    run()

# created on 2019-11-23
