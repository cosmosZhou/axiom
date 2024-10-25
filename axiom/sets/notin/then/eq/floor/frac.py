from util import *


@apply
def apply(given):
    x = given.of(NotElement[Integers])

    return Equal(floor(-frac(x)), -1)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(real=True)
    Eq << apply(NotElement(x, Integers))

    Eq << sets.notin.then.el.frac.apply(Eq[0])

    Eq << sets.el.then.el.neg.apply(Eq[-1])

    Eq << sets.el_interval.then.et.apply(Eq[-1])

    Eq <<= algebra.lt.then.lt.floor.apply(Eq[-1]), algebra.gt.then.ge.floor.apply(Eq[-2])

    Eq << algebra.lt.then.le.strengthen.apply(Eq[-2])

    Eq <<= Eq[-2] & Eq[-1]


if __name__ == '__main__':
    run()
# created on 2018-05-20
