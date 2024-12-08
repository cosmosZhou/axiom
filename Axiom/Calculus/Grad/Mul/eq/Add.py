from util import *


@apply
def apply(self):
    args, *limits_d = self.of(Derivative[Mul])
    rhs = Add(*[Derivative(arg, *limits_d) * Mul(*args[:i] + args[i + 1:]) for i, arg in enumerate(args)])
    return Equal(self, rhs)


@prove
def prove(Eq):
    from Axiom import Calculus, Algebra

    x = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Derivative[x](f(x) * g(x)))

    ε = Symbol(real=True)
    Eq <<= Eq[-1].rhs.find(Derivative).this.apply(Calculus.Grad.eq.Limit, ε), Eq[-1].rhs.args[1].find(Derivative).this.apply(Calculus.Grad.eq.Limit, ε)

    Eq.g_is_continuous = Equal(Limit[ε:0](g(x + ε)), g(x), plausible=True)

    Eq << Eq.g_is_continuous.this.lhs.doit()

    Eq <<= Eq[-2].reversed * f(x), Calculus.Eq_Limit.Eq_Limit.to.Eq_Limit.Mul.apply(Eq[-1], Eq.g_is_continuous)

    Eq << Eq[-2].this.lhs.apply(Calculus.Mul.eq.Limit)

    Eq <<= Eq[-2].this.lhs.find(Mul).apply(Algebra.Mul.eq.Add), Eq[-1].this.lhs.find(Mul).apply(Algebra.Mul.eq.Add)

    Eq << Calculus.Eq_Limit.Eq_Limit.to.Eq_Limit.Add.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.expr.apply(Algebra.Add.eq.Mul)

    Eq << Eq[-1].this.lhs.apply(Calculus.Limit.eq.Grad)





if __name__ == '__main__':
    run()
# created on 2022-01-19
# updated on 2023-06-22
