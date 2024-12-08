from util import *



@apply
def apply(given):
    fx, fy = given.of(Imply)
    return Iff(fx, fx & fy)


@prove
def prove(Eq):
    from Axiom import Algebra
    n = Symbol(integer=True, nonnegative=True)
    f, g, h = Symbol(integer=True, shape=(oo,))

    Eq << apply(Imply(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))

    Eq.suffice, Eq.necessary = Algebra.Iff.of.And.apply(Eq[1])

    Eq << Algebra.Imply_And.to.Imply.And.apply(Eq[0])



if __name__ == '__main__':
    run()

# created on 2018-02-03
