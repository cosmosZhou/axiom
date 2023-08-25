from util import *


@apply(simplify=False)
def apply(cond, suffice):
    lhs, fy = suffice.of(Infer)
    return cond, Infer(cond & lhs, fy)


@prove
def prove(Eq):
    from axiom import algebra

    a, b, c = Symbol(integer=True)
    Eq << apply(Equal(b, 0), Infer(Equal(a, 0), Equal(c, 0)))

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[0], Eq[2])

    
    


if __name__ == '__main__':
    run()
# created on 2019-08-15
# updated on 2023-06-22
