from util import *


@apply
def apply(self):
    expr, (i,) = self.of(Any)
    return Any[i](expr._subs(i, -i))


@prove
def prove(Eq):
    from Axiom import Algebra

    i = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Any[i](f(i) >= 0))

    Eq << Algebra.Any.to.Any.limits.Neg.oo.apply(Eq[-1])








if __name__ == '__main__':
    run()
# created on 2019-02-13
