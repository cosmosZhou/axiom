from util import *



@apply
def apply(given):
    q, p = given.of(Given)

    return Equal(Bool(p), Bool(p) * Bool(q))


@prove
def prove(Eq):
    from Axiom import Algebra
    n = Symbol(integer=True, nonnegative=True)
    f, h, g = Symbol(integer=True, shape=(oo,))

    Eq << apply(Given(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))

    Eq << Eq[0].reversed

    Eq << Algebra.Imply.to.Eq.Bool.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-01-28
