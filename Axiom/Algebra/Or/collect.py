from util import *


@apply
def apply(given, *, cond=None):
    from Axiom.Algebra.Or.to.Or.collect import collect
    return collect(given, cond)

@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True, given=True)
    f, h, g = Function(real=True)
    Eq << apply(Unequal(x, y) | Equal(f(x), g(y)) & (y > 0) | Equal(h(x), g(y)) & (y > 0), cond=y > 0)

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Or.to.Or.collect, cond=y > 0)
    Eq << Eq[-1].this.lhs.apply(Algebra.Or.of.Or.collect, cond=y > 0)


if __name__ == '__main__':
    run()
# created on 2020-02-16
