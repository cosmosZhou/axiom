from util import *


@apply
def apply(is_zero):
    fx, *limits = is_zero.of(Equal[Limit[Abs], 0])
    return Equal(Limit(fx, *limits), ZeroMatrix(*fx.shape))


@prove
def prove(Eq):
    from axiom import calculus

    x, x0 = Symbol(real=True)
    g = Function(real=True)
    Eq << apply(Equal(Limit[x:x0](Abs(g(x))), 0))

    Eq << calculus.eq_limit.given.any_all.limit_definition.apply(Eq[1])

    Eq << calculus.eq_limit.imply.any.all.limit_definition.apply(Eq[0])


if __name__ == '__main__':
    run()
# created on 2023-04-18
