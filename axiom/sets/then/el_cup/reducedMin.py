from util import *


@apply
def apply(self):
    return Element(ReducedMin(self), self.cup_finiteset())


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(oo,))
    Eq << apply(x[:n])

    Eq << sets.el_cup.of.any_el.apply(Eq[0])

    i = Eq[-1].variable
    Eq << algebra.any.of.cond.subs.apply(Eq[-1], i, ReducedArgMin(x[:n]))

    Eq << algebra.then.eq.reducedMin.apply(x[:n])


if __name__ == '__main__':
    run()
# created on 2023-11-12
