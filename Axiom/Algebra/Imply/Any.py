from util import *


@apply
def apply(given, var=None):
    lhs, rhs = given.of(Imply)
    assert lhs._has(var) and rhs._has(var)
    return Imply(Exists[var](lhs), Exists[var](rhs))


@prove
def prove(Eq):
    from Axiom import Algebra

    p, q, r = Function(real=True)
    x = Symbol(real=True)
    Eq << apply(Imply(p(x) >= 0, q(x) >= 0), var=x)

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Imply.to.Imply.Any, x)

    Eq << Eq[-1].this.rhs.apply(Algebra.Imply.of.Imply.Any, x)


if __name__ == '__main__':
    run()
# created on 2023-11-10
