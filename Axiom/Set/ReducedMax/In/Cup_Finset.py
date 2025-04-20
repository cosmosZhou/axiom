from util import *


@apply
def apply(self):
    return Element(ReducedMax(self), self.cup_finiteset())


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(oo,))
    Eq << apply(x[:n])

    Eq << Set.Mem_Cup.given.Any_Mem.apply(Eq[0])

    i = Eq[-1].variable
    Eq << Algebra.Any.given.Cond.subs.apply(Eq[-1], i, ReducedArgMax(x[:n]))

    Eq << Algebra.ReducedMax.eq.IndexedReducedArgMax.apply(x[:n])


if __name__ == '__main__':
    run()
# created on 2023-11-12
