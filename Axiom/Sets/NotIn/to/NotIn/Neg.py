from util import *


@apply
def apply(given):
    e, interval = given.of(NotElement)

    return NotElement(-e, -interval)


@prove
def prove(Eq):
    from Axiom import Sets
    x, a, b = Symbol(real=True, given=True)
    Eq << apply(NotElement(x, Interval(a, b)))

    Eq << ~Eq[-1]

    Eq << Sets.In.to.In.Neg.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

# created on 2018-06-19
