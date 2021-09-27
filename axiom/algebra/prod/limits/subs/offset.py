from util import *


@apply
def apply(self, offset):
    from axiom.algebra.sum.limits.subs.offset import limits_subs
    return Equal(self, limits_subs(Product, self, offset), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    n, d = Symbol(integer=True)
    f = Function(real=True)
    m = Symbol(integer=True, nonnegative=True, given=False)
    Eq << apply(Product[n:0:m](f(n)), d)

    Eq << Eq[0].subs(m, 0)

    Eq.induct = Eq[0].subs(m, m + 1)

    Eq << Eq.induct.this.lhs.apply(algebra.prod.to.mul.split, cond={m})

    Eq << Eq[-1].this.rhs.apply(algebra.prod.to.mul.split, cond={m - d})

    Eq << Eq[0] * f(m)

    Eq << Suffice(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.suffice.imply.cond.induct.apply(Eq[-1], n=m, start=0)


if __name__ == '__main__':
    run()