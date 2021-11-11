from util import *


@apply
def apply(eq, f_eq, swap=False, reverse=False, simplify=True, assumptions={}):
    from axiom.algebra.all_eq.cond.imply.all.subs import subs
    if swap:
        f_eq, eq = eq, f_eq

    old, new = eq.of(Equal)
    lhs, rhs = f_eq.of(Equal)

    if reverse:
        old, new = new, old

    return Equal(subs(lhs, old, new, simplify=simplify, assumptions=assumptions), rhs)


@prove
def prove(Eq):
    m, n = Symbol(integer=True, positive=True)
    a, b, c, d = Symbol(real=True, shape=(m, n))
    Eq << apply(Equal(a, 2 * c), Equal(a * b, d * a))

    Eq << Eq[1].subs(Eq[0])

    Eq << Eq[2].subs(Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-08-25
# updated on 2019-08-25
