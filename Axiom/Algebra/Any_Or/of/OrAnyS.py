from util import *


@apply
def apply(imply):
    ou, *limits = imply.of(Any[Or])

    return Or(*(Any(eq, *limits) for eq in ou))


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True)
    A = Symbol(etype=dtype.real, given=True)
    f, g = Function(integer=True)
    Eq << apply(Any[x:A]((g(x) > 0) | (f(x) > 0)))

    Eq <<= ~Eq[0] & Eq[1]

    Eq << Eq[-1].this.find(All).apply(Algebra.All_And.to.And.All)

    Eq << Algebra.And.to.Or.apply(Eq[-1])





if __name__ == '__main__':
    run()

# created on 2018-10-02
# updated on 2023-05-11