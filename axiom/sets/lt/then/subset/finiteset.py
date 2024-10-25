from util import *


@apply
def apply(given):
    a, b = given.of(Less)
    return Subset({b, a}, Interval(a, b))


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, y = Symbol(real=True, given=True)
    Eq << apply(x < y)

    Eq << algebra.lt.then.le.relax.apply(Eq[0])

    Eq << sets.le.then.subset.finiteset.apply(Eq[-1], simplify=None)




if __name__ == '__main__':
    run()
# created on 2023-10-22
