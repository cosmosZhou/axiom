from util import *


@apply
def apply(fx, x=None):
    from Axiom.Algebra.Eq_.Add.Zero.to.And.Imply.quartic.one_leaded import quartic_coefficient
    fx = fx.of(Equal[0])
    S[1], S[0], alpha, S[0], gamma = quartic_coefficient(fx, x=x)
    delta = alpha ** 2 - 4 * gamma
    return Equal(x, sqrt(sqrt(delta) / 2 - alpha / 2)) | Equal(x, -sqrt(sqrt(delta) / 2 - alpha / 2)) | Equal(x, sqrt(-sqrt(delta) / 2 - alpha / 2)) | Equal(x, -sqrt(-sqrt(delta) / 2 - alpha / 2))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, alpha, gamma = Symbol(complex=True, given=True)
    fx = x ** 4 + alpha * x ** 2 + gamma
    Eq << apply(Equal(fx, 0), x=x)

    y = Symbol(x ** 2)
    Eq << Eq[0].subs(y.this.definition.reversed)

    Eq << Algebra.Add.eq.Zero.to.And_Imply_Or_EqS_Div.quadratic.apply(Eq[-1], y)

    Eq << Eq[-1].subs(y.this.definition)

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.args[-1].apply(Algebra.Eq_Square.to.Or_Eq_0)

    Eq << Eq[-1].this.args[-1].apply(Algebra.Eq_Square.to.Or_Eq_0)

    Eq << Eq[-1].this.args[-1].apply(Algebra.Eq.transport)

    Eq << Eq[-1].this.args[-1].apply(Algebra.Eq.transport)

    Eq << Eq[-1].this.args[-1].apply(Algebra.Eq.transport)

    Eq << Eq[-1].this.args[-1].apply(Algebra.Eq.transport)





if __name__ == '__main__':
    run()
# created on 2018-11-26
# updated on 2023-05-17
