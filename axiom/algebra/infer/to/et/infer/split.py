from util import *


@apply
def apply(given, *, cond=None):
    p, q = given.of(Infer)
    return And(Infer(p & cond, q), Infer(p & cond.invert(), q))


@prove
def prove(Eq):
    from axiom import algebra

    f, g = Function(integer=True)
    x, y = Symbol(integer=True)
    Eq << apply(Infer(Equal(f(x), f(y)), Equal(g(x), g(y))), cond=x > 0)

    Eq << algebra.iff.of.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.infer.then.et.infer.split, cond=Eq[0].find(Greater))

    Eq << Eq[-1].this.rhs.apply(algebra.infer.of.et.infer.split, cond=Eq[0].find(Greater))


if __name__ == '__main__':
    run()
# created on 2023-04-25
