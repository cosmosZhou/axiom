from util import *


@apply
def apply(eq, f_eq, *, reverse=False, simplify=True, assumptions={}, index=None):
    from axiom.algebra.all_eq.cond.then.all.subs import subs
    lhs, rhs = eq.of(Equal)
    if reverse:
        lhs, rhs = rhs, lhs
    return eq, subs(f_eq, lhs, rhs, simplify=simplify, assumptions=assumptions, index=index)


@prove
def prove(Eq):
    from axiom import algebra

    m, n = Symbol(integer=True, positive=True)
    a, b, c = Symbol(real=True, shape=(m, n))
    S = Symbol(etype=dtype.real[m][n])
    Eq << apply(Equal(a, 2 * c), Element(a * b, S))

    Eq << algebra.iff.of.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.eq.cond.then.cond.subs)

    Eq << Eq[-1].this.lhs.apply(algebra.eq.cond.then.cond.subs, reverse=True)


if __name__ == '__main__':
    run()
# created on 2023-08-26
