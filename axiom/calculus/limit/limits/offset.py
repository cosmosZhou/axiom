from util import *


@apply
def apply(self, offset):
    fx, (x, x0) = self.of(Limit)
    fx = fx._subs(x, x + offset)

    return Equal(self, Limit[x:x0 - offset](fx))


@prove
def prove(Eq):
    from axiom import calculus, algebra

    x, x0 = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Limit[x:x0](f(x - x0)), x0)

    # we assume this limit exists and is real
    A = Symbol(Eq[0].rhs, real=True)
    Eq << A.this.definition

    Eq << calculus.eq_limit.then.any.all.limit_definition.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(algebra.all.then.all.limits.subs.offset, -x0)

    Eq << calculus.any_all.then.eq.limit_definition.apply(Eq[-1])

    Eq << algebra.eq.eq.then.eq.trans.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2020-04-05
