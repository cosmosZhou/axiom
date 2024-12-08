from util import *


@apply
def apply(given):
    x, y = given.of(LessEqual)
    return Equal(~x, x)


@prove
def prove(Eq):
    from Axiom import Sets

    x, y = Symbol(complex=True)
    Eq << apply(x <= y)

    Eq << Sets.Le.to.is_real.apply(Eq[0], simplify=None)

    Eq << Sets.is_real.to.Eq.Conj.apply(Eq[-1])









if __name__ == '__main__':
    run()
# created on 2023-05-01
# updated on 2023-05-02
