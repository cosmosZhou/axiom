from util import *


@apply
def apply(self):
    from Axiom.Algebra.All.equ.And.doit.setlimit import doit
    return Equal(self, doit(Cap, self))


@prove
def prove(Eq):
    from Axiom import Sets
    x = Symbol(etype=dtype.real, shape=(oo,))
    i, j, a, b, c, d = Symbol(integer=True)
    f = Function(integer=True)


    Eq << apply(Cap[i:{a, b, c, d}](x[i]))

    Eq << Equal(Cap[i:{a}](x[i]), x[a], plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Equal(Cap[i:{b}](x[i]), x[b], plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Sets.Eq.Eq.to.Eq.Intersect.apply(Eq[-2], Eq[-1])

    Eq << Equal(Cap[i:{c}](x[i]), x[c], plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Sets.Eq.Eq.to.Eq.Intersect.apply(Eq[-2], Eq[-1])

    Eq << Equal(Cap[i:{d}](x[i]), x[d], plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Sets.Eq.Eq.to.Eq.Intersect.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-01-17
