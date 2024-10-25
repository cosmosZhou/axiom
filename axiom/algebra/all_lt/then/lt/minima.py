from util import *


@apply
def apply(given):
    (fx, a), *limits = given.of(All[Less])
    assert Tuple.is_nonemptyset(limits)
    return Minima(fx, *limits) < a


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    S = Symbol(etype=dtype.real, given=True, empty=False)
    f = Function(shape=(), complex=True)
    M = Symbol(real=True)
    Eq << apply(All[x:S](f(x) < M))

    Eq << algebra.then.all.minima_le.apply(Eq[1].lhs)

    Eq << algebra.all.all.then.all.et.apply(Eq[0], Eq[2])

    Eq << Eq[-1].this.expr.apply(algebra.le.lt.then.lt.trans)




if __name__ == '__main__':
    run()
# created on 2023-03-25
