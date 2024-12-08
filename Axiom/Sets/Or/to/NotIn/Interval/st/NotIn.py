from util import *


@apply
def apply(given):
    equal, notcontains = given.of(Or)

    x, b = equal.of(Equal)
    S[x], ab = notcontains.of(NotElement)
    a, S[b] = ab.of(Interval)
    assert not ab.right_open

    ab = ab.copy(right_open=True)
    return NotElement(x, ab)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a, b = Symbol(real=True, given=True)
    Eq << apply(Equal(x, b) | NotElement(x, Interval(a, b)))

    Eq << ~Eq[-1]

    Eq <<= Eq[-1] & Eq[0]

    Eq << Algebra.And.to.Or.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-10-19
