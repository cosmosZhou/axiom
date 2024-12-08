from util import *


@apply
def apply(given):
    (fx, m), *limits = given.of(All[GreaterEqual])
    assert not m.has(*(v for v, *_ in limits))
    return Inf(fx, *limits) >= m


@prove
def prove(Eq):
    from Axiom import Algebra

    M, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[x:a:b](f(x) >= M))

    Eq << Eq[1].this.lhs.apply(Algebra.Inf.eq.ReducedMax)

    m = Symbol(Eq[-1].lhs)
    Eq << m.this.definition

    Eq << Algebra.Eq_ReducedMax.to.All.Ge.apply(Eq[-1])

    y = Eq[-1].variable
    Eq << Algebra.All.to.Imply.apply(Eq[-1])

    Eq << Eq[-1].subs(y, M)

    Eq << Algebra.Cond.Imply.to.Cond.trans.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.lhs.definition




if __name__ == '__main__':
    run()
# created on 2019-01-15
# updated on 2023-04-14
