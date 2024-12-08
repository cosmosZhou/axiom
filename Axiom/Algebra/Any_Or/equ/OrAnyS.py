from util import *


@apply
def apply(imply):
    ou, *limits = imply.of(Any[Or])

    return Or(*(Any(eq, *limits) for eq in ou))


@prove
def prove(Eq):
    from Axiom import Algebra
    x = Symbol(real=True)
    A = Symbol(etype=dtype.real)

    f, g = Function(integer=True)

    Eq << apply(Any[x:A]((g(x) > 0) | (f(x) > 0)))

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Any_Or.to.OrAnyS)

    Eq << Eq[-1].this.lhs.apply(Algebra.Any_Or.of.OrAnyS)


if __name__ == '__main__':
    run()

# created on 2019-02-28
