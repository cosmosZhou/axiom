from util import *


@apply
def apply(given):
    p, q = given.of(Infer)
    return p.invert()


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(integer=True)
    f, g = Function(integer=True)

    Eq << apply(Infer(x > y, f(x) > g(y)))

    Eq << Eq[0].this.apply(algebra.infer.to.ou)

    Eq << algebra.ou.of.cond.apply(Eq[-1], index=1)


if __name__ == '__main__':
    run()
# created on 2023-04-11
