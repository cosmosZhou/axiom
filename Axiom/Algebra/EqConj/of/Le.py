from util import *


@apply
def apply(given):
    x, y = given.of(LessEqual)
    return Equal(~x, x)


@prove
def prove(Eq):
    from Axiom import Set

    x, y = Symbol(complex=True)
    Eq << apply(x <= y)

    Eq << Set.IsReal.of.Le.apply(Eq[0], simplify=None)

    Eq << Set.EqConj.of.IsReal.apply(Eq[-1])









if __name__ == '__main__':
    run()
# created on 2023-05-01
# updated on 2023-05-02
