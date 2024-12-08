from util import *


@apply
def apply(given, x=None):
    from Axiom.Algebra.Le.Ge.to.Le.quadratic import quadratic_coefficient
    fx = given.of(Equal[0])

    x, a, b, c = quadratic_coefficient(fx, x=x)

    delta = b * b - 4 * a * c

    return Imply(Equal(a, 0) & Equal(b, 0), Equal(c, 0)), Imply(Equal(a, 0) & Unequal(b, 0), True if b == 0 else Equal(x, -c / b)), Imply(Unequal(a, 0), Or(Equal(x, (-b + sqrt(delta)) / (a * 2)), Equal(x, (-b - sqrt(delta)) / (a * 2))))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a, b, c = Symbol(complex=True, given=True)
    Eq << apply(Equal(a * x ** 2 + b * x + c, 0))

    Eq << Algebra.Cond.to.And.Imply.split.apply(Eq[0], cond=Equal(a, 0))

    Eq <<= Algebra.Imply_And.to.Imply.And.apply(Eq[-2]), Algebra.Imply_And.to.Imply.And.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Eq.Cond.to.Cond.subs), Eq[-1].this.rhs.apply(Algebra.Ne_0.Eq.to.Or.Eq.quadratic, x=x, simplify=False)

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Zero.to.AndImplyS_Eq.simple, x=x)

    Eq << Algebra.Imply.to.And.Imply.apply(Eq[-1])

    # Eq <<= Eq[-2].this.apply(Algebra.suffice.flatten), Eq[-1].this.apply(Algebra.suffice.flatten)


if __name__ == '__main__':
    run()
# created on 2018-08-17
