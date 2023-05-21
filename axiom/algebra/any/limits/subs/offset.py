from util import *


@apply
def apply(self, offset):
    from axiom.algebra.sum.limits.subs.offset import limits_subs
    return limits_subs(Any, self, offset)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True)
    m, d = Symbol(integer=True, given=True)
    f = Function(integer=True)
    Eq << apply(Any[n:1:m + 1](f(n) > 0), d)

    Eq << algebra.iff.given.et.infer.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(algebra.any.imply.any.limits.subs.offset, d)
    Eq << Eq[-1].this.lhs.apply(algebra.any.imply.any.limits.subs.offset, -d)


if __name__ == '__main__':
    run()
# created on 2019-02-21
