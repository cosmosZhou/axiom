from util import *


@apply
def apply(self):
    arg, *limits = self.of(Sum[Im])

    return Equal(self, Im(Sum(arg, *limits)))


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True, nonnegative=True, given=False)
    z = Symbol(complex=True, shape=(oo,))
    k = Symbol(integer=True)
    Eq << apply(Sum[k:n](Im(z[k])))

    Eq << Eq[0].subs(n, n + 1)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.rhs.arg.apply(Algebra.Sum.eq.Add.pop)

    Eq << Imply(Eq[0], Eq[1], plausible=True)

    Eq << Algebra.Imply.to.Cond.induct.apply(Eq[-1], n, 0)


if __name__ == '__main__':
    run()
# created on 2023-06-03
