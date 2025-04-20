from util import *


@apply
def apply(self):
    *t, x = self.of(Expr * Log)
    t = Mul(*t)
    rhs = log(x ** t)
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra

    t = Symbol(real=True)
    x = Symbol(real=True, positive=True)
    Eq << apply(t * log(x))

    Eq << Algebra.Eq.given.Eq.Exp.apply(Eq[0])

    y = Symbol(log(x))
    Eq << y.this.definition

    Eq <<= Eq[-1] * t, Algebra.EqExp.of.Eq.apply(Eq[-1])

    Eq <<= Algebra.EqExp.of.Eq.apply(Eq[-2]), Algebra.EqPowS.of.Eq.apply(Eq[-1], exp=t)
    Eq << Algebra.Eq.of.Eq.Eq.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-01-29
