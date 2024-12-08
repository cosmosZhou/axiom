from util import *


@apply
def apply(given):
    lhs, *limits = given.of(All[Equal[0]])
    shape = given.limits_shape

    return Equal(Lamda(lhs, *limits), ZeroMatrix(*shape, *lhs.shape))


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True, positive=True, given=True)
    i = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(All[i:n](Equal(f(i), 0)))

    j = Symbol(domain=Range(n))
    Eq << Algebra.Eq.of.Eq.getitem.apply(Eq[1], j)

    Eq << Algebra.All.to.Cond.subs.apply(Eq[0], i, j)


if __name__ == '__main__':
    run()
# created on 2022-01-01
