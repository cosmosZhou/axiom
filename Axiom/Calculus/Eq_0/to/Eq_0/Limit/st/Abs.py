from util import *


@apply
def apply(is_zero):
    fx, *limits = is_zero.of(Equal[Limit[Abs], 0])
    return Equal(Limit(fx, *limits), ZeroMatrix(*fx.shape))


@prove
def prove(Eq):
    from Axiom import Calculus

    x, x0 = Symbol(real=True)
    g = Function(real=True)
    Eq << apply(Equal(Limit[x:x0](Abs(g(x))), 0))

    Eq << Calculus.Eq_Limit.of.Any_All.limit_definition.apply(Eq[1])

    Eq << Calculus.Eq_Limit.to.Any.All.limit_definition.apply(Eq[0])


if __name__ == '__main__':
    run()
# created on 2023-04-18
