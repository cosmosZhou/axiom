from util import *


@apply
def apply(self):
    expr, *limits = self.of(Product)

    return Equal(self, self.func(expr ** Bool(self.limits_cond), *((x,) for x, *_ in limits)))


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    S = Symbol(etype=dtype.integer)
    x = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Product[x:S](f(x)))

    Eq << Eq[0].this.find(Bool).apply(Logic.Bool.eq.Ite)

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.Pow.eq.Ite.exponent)




if __name__ == '__main__':
    run()

# created on 2018-04-13
# updated on 2023-04-23
