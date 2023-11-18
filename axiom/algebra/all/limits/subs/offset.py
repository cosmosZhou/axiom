from util import *


@apply
def apply(self, index=0, offset=None):
    from axiom.algebra.sum.limits.subs.offset import limits_subs
    return limits_subs(All, self, index, offset, simplify=False)


@prove
def prove(Eq):
    from axiom import algebra

    n, m, d = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(All[n:1:m + 1](f(n) > 0), d)

    Eq << algebra.iff.given.et.infer.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(algebra.all.imply.all.limits.subs.offset, d)

    Eq << Eq[-1].this.rhs.apply(algebra.all.given.all.limits.subs.offset, d)


if __name__ == '__main__':
    run()
# created on 2018-12-20
