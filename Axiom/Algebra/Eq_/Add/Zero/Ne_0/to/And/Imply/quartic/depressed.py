from util import *


def solver_set(d, A, B, x, alpha, beta, w, offset=0):
    if d == 0:
        y = A + B
    elif d % 3 == 1:
        y = A * w + B
    elif d % 3 == 2:
        y = A * ~w + B
    else:
        ...

    y0 = -2 * alpha / 3 + y
    y1 = 4 * alpha / 3 + y

    x0 = sqrt(2 * beta / sqrt(y0) - y1) / 2 - sqrt(y0) / 2 + offset
    x1 = -sqrt(2 * beta / sqrt(y0) - y1) / 2 - sqrt(y0) / 2 + offset
    x2 = sqrt(-2 * beta / sqrt(y0) - y1) / 2 + sqrt(y0) / 2 + offset
    x3 = -sqrt(-2 * beta / sqrt(y0) - y1) / 2 + sqrt(y0) / 2 + offset

    return Equal(x, x0) | Equal(x, x1) | Equal(x, x2) | Equal(x, x3)


@apply
def apply(fx, is_nonzero, x=None):
    from Axiom.Algebra.Eq_.Add.Zero.to.And.Imply.quartic.one_leaded import quartic_coefficient
    from Axiom.Algebra.Eq_.Add.Zero.of.And.Eq.cubic.one_leaded import cubic_solve
    from Axiom.Algebra.Ne_0.Eq_.Add.Zero.to.Ne import cubic_delta
    fx = fx.of(Equal[0])
    S[1], S[0], alpha, beta, gamma = quartic_coefficient(fx, x=x)

    w = -S.One / 2 + sqrt(3) * S.ImaginaryUnit / 2

    y_delta = cubic_delta(x, alpha, beta, gamma)
    _d, Y0, Y1, Y2 = cubic_solve(y_delta, x)

    S[beta] = is_nonzero.of(Unequal[0])

    delta = -(alpha ** 2 / 3 + 4 * gamma) ** 3 / 27 + (-alpha ** 3 / 27 + 4 * alpha * gamma / 3 - beta ** 2 / 2) ** 2

    V = alpha ** 3 / 27 - 4 * alpha * gamma / 3 + beta ** 2 / 2 - sqrt(delta)
    U = alpha ** 3 / 27 - 4 * alpha * gamma / 3 + beta ** 2 / 2 + sqrt(delta)

    A = U ** (S.One / 3)
    B = V ** (S.One / 3)

    return Imply(Equal(_d, 0), solver_set(0, A, B, x, alpha, beta, w)), Imply(Equal(_d % 3, 1), solver_set(1, A, B, x, alpha, beta, w)), Imply(Equal(_d % 3, 2), solver_set(2, A, B, x, alpha, beta, w))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, alpha, beta, gamma = Symbol(complex=True, given=True)
    fx = x ** 4 + alpha * x ** 2 + beta * x + gamma
    Eq << apply(Equal(fx, 0), Unequal(beta, 0), x=x)

    Eq << Algebra.Cond.to.Imply.apply(Eq[0] & Eq[1], cond=Eq[2].lhs)

    Eq << Algebra.Imply_And.to.Imply.And.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq_.Add.Zero.Eq_.Add.Zero.Ne_0.to.Or_Eq.quartic.depressed, x)

    Eq << Algebra.Cond.to.Imply.apply(Eq[0] & Eq[1], cond=Eq[3].lhs)

    Eq << Algebra.Imply_And.to.Imply.And.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq_.Add.Zero.Eq_.Mod.Zero.Ne_0.to.Or_Eq.quartic.depressed, x)

    Eq << Algebra.Cond.to.Imply.apply(Eq[0] & Eq[1], cond=Eq[4].lhs)

    Eq << Algebra.Imply_And.to.Imply.And.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq_.Add.Zero.Eq_.Mod.Zero.Ne_0.to.Or_Eq.quartic.depressed, x)

    # https://planetmath.org/QuarticFormula
    # https://en.wikipedia.org/wiki/Quartic_equation


if __name__ == '__main__':
    run()
# created on 2018-11-27
