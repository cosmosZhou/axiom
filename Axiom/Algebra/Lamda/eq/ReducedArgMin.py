from util import *


@apply
def apply(self):
    expr, *limits = self.of(Lamda[ReducedArgMin])
    return Equal(self, ReducedArgMin(Lamda(expr, *limits).simplify()))


@prove
def prove(Eq):
    from Axiom import Algebra
    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    a = Symbol(shape=(oo, n), real=True)
    Eq << apply(Lamda[i:n](ReducedArgMin(a[i])))

    i = Symbol(domain=Range(n))
    Eq << Algebra.Eq.of.Eq.getitem.apply(Eq[0], i)


if __name__ == '__main__':
    run()
# created on 2021-12-20