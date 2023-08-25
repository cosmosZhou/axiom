from util import *


@apply
def apply(self):
    args = self.of(Norm[Mul])
    import std
    vector, coeffs = std.array_split(args, lambda arg: arg.shape)
    return Equal(self, abs(Mul(*coeffs)) * Norm(Mul(*vector)))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    a = Symbol(complex=True)
    Eq << apply(Norm(x * a))

    Eq << Eq[0].this.lhs.apply(algebra.norm.to.sqrt)

    Eq << Eq[-1].this.find(Norm).apply(algebra.norm.to.sqrt)

    Eq << Eq[-1].this.find(Abs ** 2).apply(algebra.square_abs.to.mul.conj)

    Eq << Eq[-1].this.find(Expr * Conjugate).args[:2].apply(algebra.mul_conj.to.square.abs)

    Eq << Eq[-1].this.find(Expr * Conjugate).apply(algebra.mul_conj.to.square.abs)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.domain_defined)


if __name__ == '__main__':
    run()
# created on 2023-06-24
