from util import *


@apply(simplify=False)
def apply(given):
    cond, fy = given.of(Imply)
    return Imply(cond, cond & fy)


@prove
def prove(Eq):
    from Axiom import Algebra

    a, b, c = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))
    Eq << apply(Imply(Equal(a, 0), Equal(c, 0)))


    Eq << Algebra.Imply.of.And.Imply.apply(Eq[1])



if __name__ == '__main__':
    run()
# created on 2023-05-03

from . import both_sided
from . import domain_defined
