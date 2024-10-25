from util import *


@apply
def apply(given):
    fx, fy = given.of(Assuming)
    return Infer(fy, fx)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True)
    f, g = Function(integer=True)
    Eq << apply(Assuming(f(n) < g(n), f(n + 1) < g(n + 1)))

    Eq << algebra.iff.of.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.assuming.then.infer.reverse)

    Eq << Eq[-1].this.rhs.apply(algebra.assuming.of.infer.reverse)


if __name__ == '__main__':
    run()
# created on 2019-03-05
