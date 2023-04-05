from util import *


# given: x | y = x
# imply: x | y & z = x | z
@apply
def apply(ne, eq):
    [*conds] = ne.of(Unequal[Probability[And], 0])
    lhs, _x = eq.of(Equal)
    if lhs.is_Probability:
        _x = _x.of(Probability)
        lhs = lhs.arg

    x, given = lhs.of(Conditioned)
    assert x == _x

    if given.is_And:
        for g in given.args:
            del conds[conds.index(g)]
    else:
        del conds[conds.index(given)]

    z = And(*conds)
    if x.is_symbol:
        return Equal(x | given & z, x | z)
    else:
        return Equal(Probability(x, given=given & z), Probability(x, given=z))


@prove(provable=False)
def prove(Eq):
    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Unequal(Probability(y, z), 0), Equal(x | y, x))

    

    

    
    


if __name__ == '__main__':
    run()
# created on 2020-12-16
# updated on 2023-04-02

from . import st
