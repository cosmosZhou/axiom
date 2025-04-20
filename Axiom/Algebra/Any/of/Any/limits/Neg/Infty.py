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

    Eq << ~Eq[1]

    Eq << Eq[-1].simplify()

    Eq << Eq[-1].subs(i, -i)

    Eq << Algebra.Any.And.of.Cond.Any.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2018-07-10
