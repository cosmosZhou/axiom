from util import *


@apply
def apply(given):
    (fx, a), *limits = given.of(All[Less])
    assert Tuple.is_nonemptyset(limits)
    return Minima(fx, *limits) < a


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True)
    S = Symbol(etype=dtype.real, given=True, empty=False)
    f = Function(shape=(), complex=True)
    M = Symbol(real=True)
    Eq << apply(All[x:S](f(x) < M))

    Eq << Algebra.All_LeMinima.apply(Eq[1].lhs)

    Eq << Algebra.All.All.to.All.And.apply(Eq[0], Eq[2])

    Eq << Eq[-1].this.expr.apply(Algebra.Le.Lt.to.Lt.trans)




if __name__ == '__main__':
    run()
# created on 2023-03-25
