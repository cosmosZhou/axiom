from util import *


@apply
def apply(ne, eq):
    z, _y = ne.of(Unequal[Probability[Conditioned], 0])

    lhs, x = eq.of(Equal)
    if lhs.is_Probability:
        lhs = lhs.arg
        x = x.of(Probability)

    S[x], y = lhs.of(Conditioned)

    if _y != y:
        _y, z = z, _y

    assert _y == y

    if x.is_bool:
        return Equal(Probability(x, given=y & z), Probability(x, given=z))
    return Equal(x | y & z, x | z)


@prove
def prove(Eq):
    from Axiom import Stats

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Unequal(Probability(z | y), 0), Equal(x | y, x))

    Eq << Stats.Ne_0.to.Ne_0.joint.apply(Eq[0])

    Eq << Stats.Ne_0.Eq_Conditioned.to.Eq.Conditioned.joint.apply(Eq[-1], Eq[1])



if __name__ == '__main__':
    run()
# created on 2020-12-15
# updated on 2023-04-02
