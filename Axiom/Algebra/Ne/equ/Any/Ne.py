from util import *


def rewrite(self, i):
    lhs, rhs = self.of(Unequal)
    if i is None:
        if lhs.is_Lamda:
            i = lhs.variables[-1]
        elif rhs.is_Lamda:
            i = rhs.variable[-1]
        else:
            i = self.generate_var(integer=True)

    return Any[i:lhs.shape[0]](Unequal(lhs[i], rhs[i]))

@apply
def apply(self, i=None):
    return rewrite(self, i)


@prove
def prove(Eq):
    from Axiom import Algebra

    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f, g = Symbol(shape=(oo,), real=True)
    Eq << apply(Unequal(Lamda[k:n](f[k]), Lamda[k:n](g[k])))

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Ne.to.Any.Ne)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ne.of.Any.Ne)


if __name__ == '__main__':
    run()
# created on 2023-05-01
