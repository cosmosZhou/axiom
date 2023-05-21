from util import *


@apply(simplify=False)
def apply(given):
    cond, fy = given.of(Infer)
    return Infer(cond, cond & fy)


@prove
def prove(Eq):
    from axiom import algebra

    a, b, c = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))
    Eq << apply(Infer(Equal(a, 0), Equal(c, 0)))

    
    Eq << algebra.infer.given.et.infer.apply(Eq[1])
    


if __name__ == '__main__':
    run()
# created on 2023-05-03


from . import both_sided
from . import domain_defined