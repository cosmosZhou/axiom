from util import *


@apply
def apply(given):
    n = given.of(Equal[Expr % 2, 0])
    return Equal(n // 2, (n + 1) // 2)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True)
    Eq << apply(Equal(n % 2, 0))

    Eq << algebra.is_even.imply.is_odd.apply(Eq[0])

    Eq << algebra.is_odd.imply.eq.floor.apply(Eq[-1])

    Eq << Eq[-3].subs(Eq[-1])

    Eq << algebra.is_even.imply.eq.floor.apply(Eq[0])

    

    


if __name__ == '__main__':
    run()
# created on 2023-05-30
