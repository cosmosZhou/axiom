from util import *


@apply
def apply(given, *, cond=None):
    if cond.is_Inference:
        cond = cond.cond
    p, q = given.of(Imply)

    return Imply(p & cond, q), p.invert() | cond


@prove
def prove(Eq):
    from Axiom import Algebra

    f, g = Function(integer=True)
    x, y = Symbol(integer=True)
    Eq << apply(Imply(Equal(f(x), f(y)), Equal(g(x), g(y))), cond=x > 0)

    Eq << Algebra.Imply.of.And.Imply.split.apply(Eq[0], cond=x > 0)

    Eq << Algebra.Imply.of.Cond.invert.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-10-03
