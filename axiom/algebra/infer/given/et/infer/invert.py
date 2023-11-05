from util import *


@apply
def apply(given, *, cond=None):
    if cond.is_Inference:
        cond = cond.cond
    p, q = given.of(Infer)

    return Infer(p & cond, q), p.invert() | cond


@prove
def prove(Eq):
    from axiom import algebra

    f, g = Function(integer=True)
    x, y = Symbol(integer=True)
    Eq << apply(Infer(Equal(f(x), f(y)), Equal(g(x), g(y))), cond=x > 0)

    Eq << algebra.infer.given.et.infer.split.apply(Eq[0], cond=x > 0)

    Eq << algebra.infer.given.cond.invert.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-10-03
