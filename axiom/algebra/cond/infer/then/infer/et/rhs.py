from util import *


@apply
def apply(cond, suffice):
    p, q = suffice.of(Infer)
    return Infer(p, q & cond)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, a, b = Symbol(integer=True)
    f, g = Function(real=True)
    Eq << apply(a > b, Infer(x > y, f(x) > g(y)))

    Eq << algebra.infer.of.et.infer.apply(Eq[-1])

    Eq << algebra.infer.of.ou.apply(Eq[-1])

    Eq << algebra.cond.then.ou.apply(Eq[0], cond=x <= y)


if __name__ == '__main__':
    run()
# created on 2018-09-12
