from util import *


@apply
def apply(self):
    return Element(ReducedMin(self), self.cup_finiteset())


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(oo,))
    Eq << apply(x[:n])

    Eq << Sets.In_Cup.of.Any_In.apply(Eq[0])

    i = Eq[-1].variable
    Eq << Algebra.Any.of.Cond.subs.apply(Eq[-1], i, ReducedArgMin(x[:n]))

    Eq << Algebra.ReducedMin.eq.IndexedReducedArgMin.apply(x[:n])


if __name__ == '__main__':
    run()
# created on 2023-11-12
