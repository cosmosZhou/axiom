from util import *


@apply
def apply(given):
    x, y = given.of(GreaterEqual)
    return Equal(~x, x)


@prove
def prove(Eq):
    from axiom import sets

    x, y = Symbol(complex=True)
    Eq << apply(x >= y)

    Eq << sets.ge.imply.is_real.apply(Eq[0], simplify=None)

    Eq << sets.is_real.imply.eq.conj.apply(Eq[-1])
    

    

    

    


if __name__ == '__main__':
    run()
# created on 2023-05-01
# updated on 2023-05-02
