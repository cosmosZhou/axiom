from util import *


@apply
def apply(given):
    e, s = given.of(NotElement)
    space, *shape = s.of(CartesianSpace)
    k = given.generate_var(integer=True)
    n = e.shape[0]
    return Exists[k:n](NotElement(e[k], CartesianSpace(space, *shape[1:])).simplify())


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    n, m = Symbol(positive=True, integer=True)
    x = Symbol(integer=True, shape=(n,))
    i = Symbol(integer=True)
    Eq << apply(NotElement(Lamda[i:n](x[i]), CartesianSpace(Range(0, m), n)))

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Sets.NotIn.to.Any.NotIn)

    Eq << Eq[-1].this.rhs.apply(Sets.NotIn.of.Any.NotIn)


if __name__ == '__main__':
    run()
# created on 2023-07-02
