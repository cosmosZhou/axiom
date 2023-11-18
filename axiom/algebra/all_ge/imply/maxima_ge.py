from util import *


@apply
def apply(given):
    (fx, m), *limits = given.of(All[GreaterEqual])
    assert Tuple.is_nonemptyset(limits)

    return GreaterEqual(Maxima(fx, *limits), m)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    S = Symbol(etype=dtype.real, given=True, empty=False)
    f = Function(shape=(), complex=True)
    m = Symbol(real=True)
    Eq << apply(All[x:S](f(x) >= m))

    Eq << algebra.imply.all.maxima_ge.apply(Eq[1].lhs)

    Eq << algebra.all.all.imply.all.et.apply(Eq[0], Eq[2])

    Eq << Eq[-1].this.expr.apply(algebra.ge.ge.imply.ge.transit)




if __name__ == '__main__':
    run()
# created on 2023-03-25
