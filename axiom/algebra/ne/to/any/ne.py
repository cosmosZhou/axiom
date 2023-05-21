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
    from axiom import algebra

    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f, g = Symbol(shape=(oo,), real=True)
    Eq << apply(Unequal(Lamda[k:n](f[k]), Lamda[k:n](g[k])))

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.ne.imply.any.ne)

    Eq << Eq[-1].this.rhs.apply(algebra.ne.given.any.ne)


if __name__ == '__main__':
    run()
# created on 2023-05-01
