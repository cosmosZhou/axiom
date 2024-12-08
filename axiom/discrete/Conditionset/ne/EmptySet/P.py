from util import *


@apply
def apply(n):
    assert n > 0
    x = Symbol(integer=True, nonnegative=True, shape=(oo,))
    P = Symbol(conditionset(x[:n], Equal(x[:n].cup_finiteset(), Range(n))))
    return Unequal(P, P.etype.emptySet)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    n = Symbol(integer=True, positive=True, given=True)
    Eq << apply(n)

    x = Eq[0].rhs.variable.base
    P = Eq[0].lhs
    Eq << Any[x[:n]](Element(x[:n] , P), plausible=True)

    Eq << Sets.Any_In.to.Ne_EmptySet.apply(Eq[-1])

    Eq << Eq[-1].this.expr.rhs.definition

    i = Symbol(integer=True)
    Eq << Algebra.Any.of.Cond.subs.apply(Eq[-1], x[:n], Lamda[i:n](i))

    Eq << Algebra.And.of.And.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.simplify()

    Eq << Sets.In_CartesianSpace.of.All.In.apply(Eq[-1])









if __name__ == '__main__':
    run()
# created on 2020-11-06
# updated on 2023-08-20
