from util import *


@apply
def apply(self):
    (expr, *limits_s), *limits_i = self.of(Integral[Sum])

    return Equal(self, Sum(Integral(expr, *limits_i), *limits_s), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra, calculus

    n = Symbol(integer=True, nonnegative=True, given=False)
    k = Symbol(integer=True)
    x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Integral[x:a:b](Sum[k:n](f[k](x))))

    Eq << Eq[0].subs(n, 0)

    Eq << Eq[0].subs(n, n + 1)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.add.pop)

    Eq << Eq[-1].this.lhs.find(Sum).apply(algebra.sum.to.add.pop)

    Eq << Eq[-1].this.lhs.apply(calculus.integral.to.add)

    Eq << Infer(Eq[0], Eq[1], plausible=True)

    Eq << algebra.infer.imply.eq.induct.apply(Eq[-1], n)


if __name__ == '__main__':
    run()
# created on 2023-04-04
