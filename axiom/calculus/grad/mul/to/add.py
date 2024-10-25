from util import *


@apply
def apply(self):
    args, *limits_d = self.of(Derivative[Mul])
    rhs = Add(*[Derivative(arg, *limits_d) * Mul(*args[:i] + args[i + 1:]) for i, arg in enumerate(args)])
    return Equal(self, rhs)


@prove
def prove(Eq):
    from axiom import calculus, algebra

    x = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Derivative[x](f(x) * g(x)))

    ε = Symbol(real=True)
    Eq <<= Eq[-1].rhs.find(Derivative).this.apply(calculus.grad.to.limit, ε), Eq[-1].rhs.args[1].find(Derivative).this.apply(calculus.grad.to.limit, ε)

    Eq.g_is_continuous = Equal(Limit[ε:0](g(x + ε)), g(x), plausible=True)

    Eq << Eq.g_is_continuous.this.lhs.doit()

    Eq <<= Eq[-2].reversed * f(x), calculus.eq_limit.eq_limit.then.eq_limit.mul.apply(Eq[-1], Eq.g_is_continuous)

    Eq << Eq[-2].this.lhs.apply(calculus.mul.to.limit)

    Eq <<= Eq[-2].this.lhs.find(Mul).apply(algebra.mul.to.add), Eq[-1].this.lhs.find(Mul).apply(algebra.mul.to.add)

    Eq << calculus.eq_limit.eq_limit.then.eq_limit.add.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.expr.apply(algebra.add.to.mul)

    Eq << Eq[-1].this.lhs.apply(calculus.limit.to.grad)





if __name__ == '__main__':
    run()
# created on 2022-01-19
# updated on 2023-06-22
