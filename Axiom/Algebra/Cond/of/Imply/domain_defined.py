from util import *


@apply
def apply(given):
    return given.domain_definition() >> given


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True, positive=True)
    f = Function(complex=True, shape=())
    x = Symbol(complex=True, shape=(n,))
    Eq << apply(1 / f(x) > 0)

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[0], cond=Eq[1].lhs)

    Eq << Eq[0].cond.invert().this.apply(Algebra.Cond.to.Cond.domain_defined)

    Eq << Eq[-1].this.apply(Algebra.Imply.contraposition)




if __name__ == '__main__':
    run()
# created on 2023-10-13
