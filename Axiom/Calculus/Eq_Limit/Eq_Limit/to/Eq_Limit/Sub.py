from util import *


@apply
def apply(limited_f, limited_g):
    (fx, (x, x0)), A = limited_f.of(Equal[Limit])
    (gx, S[(x, x0)]), B = limited_g.of(Equal[Limit])

    return Equal(Limit[x:x0](fx - gx), A - B)


@prove
def prove(Eq):
    from Axiom import Sets, Calculus

    x, x0, A, B = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Equal(Limit[x:x0](f(x)), A), Equal(Limit[x:x0](g(x)), B))

    Eq << Sets.Eq.to.is_real.apply(Eq[0], simplify=None)

    Eq << Sets.Eq.to.is_real.apply(Eq[1], simplify=None)

    Eq << Calculus.is_limited.is_limited.to.Eq.Sub.algebraic_limit_theorem.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].subs(Eq[0], Eq[1])


if __name__ == '__main__':
    run()
# created on 2020-05-19