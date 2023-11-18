from util import *


@apply
def apply(given, var=None):
    lhs, rhs = given.of(Infer)
    assert lhs._has(var) and rhs._has(var)
    return Infer(Exists[var](lhs), Exists[var](rhs))


@prove
def prove(Eq):
    from axiom import algebra

    p, q, r = Function(real=True)
    x = Symbol(real=True)
    Eq << apply(Infer(p(x) >= 0, q(x) >= 0), var=x)

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.infer.imply.infer.any, x)

    Eq << Eq[-1].this.rhs.apply(algebra.infer.given.infer.any, x)


if __name__ == '__main__':
    run()
# created on 2023-11-10
