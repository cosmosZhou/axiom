from util import *


@apply(simplify=None)
def apply(given):
    n, b = given.of(Less)
    assert n.is_finite
    return Element(n, Interval.open(-oo, b))


@prove
def prove(Eq):
    n, b = Symbol(real=True, given=True)
    Eq << apply(n < b)

    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()

# created on 2018-04-06

del Ge
from . import Ge
del Gt
from . import Gt
del Le
from . import Le
del Lt
from . import Lt
from . import average
