from util import *


@apply
def apply(self):
    expr, (i,) = self.of(Any)
    return Any[i](expr._subs(i, -i))


@prove
def prove(Eq):
    from axiom import algebra

    i, a, b, c = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Any[i](f(i) >= 0))

    Eq << algebra.iff.of.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.any.then.any.limits.negate.oo)

    Eq << Eq[-1].this.lhs.apply(algebra.any.then.any.limits.negate.oo)


if __name__ == '__main__':
    run()
# created on 2018-07-10
