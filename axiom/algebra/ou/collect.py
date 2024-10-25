from util import *


@apply
def apply(given, *, cond=None):
    from axiom.algebra.ou.then.ou.collect import collect
    return collect(given, cond)

@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True, given=True)
    f, h, g = Function(real=True)
    Eq << apply(Unequal(x, y) | Equal(f(x), g(y)) & (y > 0) | Equal(h(x), g(y)) & (y > 0), cond=y > 0)

    Eq << algebra.iff.of.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.ou.then.ou.collect, cond=y > 0)
    Eq << Eq[-1].this.lhs.apply(algebra.ou.of.ou.collect, cond=y > 0)


if __name__ == '__main__':
    run()
# created on 2020-02-16
