from util import *


@apply
def apply(given):
    return given.domain_definition() >> given


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    f = Function(complex=True, shape=())
    x = Symbol(complex=True, shape=(n,))
    Eq << apply(1 / f(x) > 0)

    Eq << algebra.cond.given.et.infer.split.apply(Eq[0], cond=Eq[1].lhs)

    Eq << Eq[0].cond.invert().this.apply(algebra.cond.imply.cond.domain_defined)

    Eq << Eq[-1].this.apply(algebra.infer.contraposition)




if __name__ == '__main__':
    run()
# created on 2023-10-13
