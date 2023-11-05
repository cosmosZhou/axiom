from util import *


@apply
def apply(given, ε=None, δ=None, var=None):
    from axiom.calculus.is_limited.imply.any.all.limit_definition import of_limited
    from axiom.calculus.eq.to.any_all.limit_definition import any_all
    fn, (x, x0), *R = of_limited(given)

    A = fn.generate_var(excludes={x}, **fn.type.dict)

    cond = any_all(Equal(given.lhs, A), ε, δ)
    B = fn.generate_var(excludes={x}, definition=given.lhs, var=var)
    return cond._subs(A, B)


@prove
def prove(Eq):
    from axiom import calculus

    x = Symbol(integer=True)
    f = Function(real=True, shape=())
    Eq << apply(Element(Limit[x:oo](f(x)), Reals), var='A')

    Eq << calculus.is_limited.imply.any.all.limit_definition.apply(Eq[0])

    Eq << Eq[-1].subs(Eq[1].reversed)


if __name__ == '__main__':
    run()
# created on 2020-04-08
