from util import *


@apply
def apply(given):
    (fx, M), *limits = given.of(All[Greater])
    return Minima(fx, *limits) > M


@prove
def prove(Eq):
    from axiom import algebra

    M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    f = Function(real=True)
    S = Symbol(etype=dtype.real, given=True)
    Eq << apply(All[x:S](f(x) > M))


    Eq << ~Eq[-1]
    Eq << algebra.minima_le.imply.any.le.apply(Eq[-1])
    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2019-12-01
# updated on 2023-11-12
