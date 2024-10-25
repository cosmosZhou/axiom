from util import *


@apply
def apply(self):
    expr, (x, x0) = self.of(Limit)
    factors, coefficient = std.array_split(expr.of(Mul), lambda arg: arg._has(x))

    coefficient = Mul(*coefficient)
    factors = Mul(*factors)

    limited = Limit[x:x0](factors).simplify()
    return Equal(self, coefficient * limited)


@prove
def prove(Eq):
    from axiom import calculus, algebra

    x, x0 = Symbol(real=True)
    y = Symbol(real=True, zero=False)
    f = Function(real=True)
    Eq << apply(Limit[x:x0](f(x) * y))

    A = Symbol(Eq[0].rhs.args[1], real=True)
    Eq << A.this.definition

    epsilon, delta = Symbol(positive=True)
    Eq << calculus.eq_limit.then.any.all.limit_definition.apply(Eq[1], epsilon=epsilon, delta=delta)

    Eq << Eq[-1].this.find(Less) * abs(y)

    Eq << Eq[-1].subs(epsilon, epsilon / abs(y))

    Eq.lhs = Equal(Eq[0].lhs, A * y, plausible=True)

    Eq << Eq.lhs.this.apply(calculus.eq.to.any_all.limit_definition, epsilon=epsilon, delta=delta)

    Eq << Eq[-1].this.expr.expr.find(Add).apply(algebra.add.to.mul)

    Eq << Eq[-1].this.find(Abs[Mul]).apply(algebra.abs.to.mul)

    Eq << algebra.eq.eq.then.eq.trans.apply(Eq.lhs, Eq[1] * y)




if __name__ == '__main__':
    run()
# created on 2020-04-20
# updated on 2023-05-20
