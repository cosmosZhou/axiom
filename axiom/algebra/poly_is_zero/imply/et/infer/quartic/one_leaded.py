from util import *


def quartic_coefficient(fx, x):
    fx = fx.as_poly(x)
    if fx.degree() != 4:
        return None
    a = fx.nth(4)
    b = fx.nth(3)
    c = fx.nth(2)
    d = fx.nth(1)
    e = fx.nth(0)
    return a, b, c, d, e

@apply
def apply(given, x=None):
    fx, rhs = given.of(Equal)
    if not rhs.is_Zero:
        fx -= rhs
    if x is None:
        for x in fx.free_symbols:
            p = fx.as_poly(x)
            if p and p.degree() == 4:
                break
        else:
            return

    _1, a, b, c, d = quartic_coefficient(fx, x=x)
    assert _1 == 1
    alpha = b - 3 * a ** 2 / 8
    beta = a ** 3 / 8 + c - a * b / 2
    gamma = a ** 2 * b / 16 + d - 3 * a ** 4 / 256 - a * c / 4

    w = -S.One / 2 + sqrt(3) * S.ImaginaryUnit / 2
    from axiom.algebra.ne_zero.poly_is_zero.imply.ne import cubic_delta
    from axiom.algebra.poly_is_zero.given.et_eq.cubic.one_leaded import cubic_solve
    y_delta = cubic_delta(x, alpha, beta, gamma)
    _d, Y0, Y1, Y2 = cubic_solve(y_delta, x)

    delta = -(alpha ** 2 / 3 + 4 * gamma) ** 3 / 27 + (-alpha ** 3 / 27 + 4 * alpha * gamma / 3 - beta ** 2 / 2) ** 2

    V = alpha ** 3 / 27 - 4 * alpha * gamma / 3 + beta ** 2 / 2 - sqrt(delta)
    U = alpha ** 3 / 27 - 4 * alpha * gamma / 3 + beta ** 2 / 2 + sqrt(delta)

    A = U ** (S.One / 3)
    B = V ** (S.One / 3)

    from axiom.algebra.poly_is_zero.ne_zero.imply.et.infer.quartic.depressed import solver_set
    delta = alpha ** 2 - 4 * gamma

    return Infer(Equal(beta, 0), Equal(x, sqrt(sqrt(delta) / 2 - alpha / 2) - a / 4) | Equal(x, -sqrt(sqrt(delta) / 2 - alpha / 2) - a / 4) | Equal(x, sqrt(-sqrt(delta) / 2 - alpha / 2) - a / 4) | Equal(x, -sqrt(-sqrt(delta) / 2 - alpha / 2) - a / 4)),\
            Infer(Unequal(beta, 0) & Equal(_d, 0), solver_set(0, A, B, x, alpha, beta, w, -a / 4)),\
            Infer(Unequal(beta, 0) & Equal(_d % 3, 1), solver_set(1, A, B, x, alpha, beta, w, -a / 4)),\
            Infer(Unequal(beta, 0) & Equal(_d % 3, 2), solver_set(2, A, B, x, alpha, beta, w, -a / 4))



@prove(slow=True)
def prove(Eq):
    from axiom import algebra

    x, a, b, c, d = Symbol(complex=True, given=True)
    Eq << apply(Equal(x ** 4 + a * x ** 3 + b * x ** 2 + c * x + d, 0), x=x)

    x = Symbol(x + a / 4)
    Eq.x_def = x.this.definition

    Eq << Eq.x_def.this.apply(algebra.eq.transport, rhs=0).reversed

    Eq << Eq[0].subs(Eq[-1])

    Eq << Eq[-1].this.find(Pow[Add]).apply(algebra.pow.to.add, simplify=None)

    Eq << Eq[-1].this.find(Pow[Add]).apply(algebra.pow.to.add, simplify=None)

    Eq << Eq[-1].this.find(Pow[Add]).apply(algebra.pow.to.add, simplify=None)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add, simplify=None)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add, simplify=None)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add, simplify=None)

    Eq << algebra.poly_is_zero.imply.et.infer.quartic.depressed.apply(Eq[-1], x)

    Eq <<= Eq[-4].subs(Eq.x_def), Eq[-3].subs(Eq.x_def), Eq[-2].subs(Eq.x_def), Eq[-1].subs(Eq.x_def)

    Eq <<= Eq[-4].this.rhs.apply(algebra.ou_eq.offset, -a / 4), Eq[-3].this.rhs.apply(algebra.ou_eq.offset, -a / 4), Eq[-2].this.rhs.apply(algebra.ou_eq.offset, -a / 4), Eq[-1].this.rhs.apply(algebra.ou_eq.offset, -a / 4)


if __name__ == '__main__':
    run()
# created on 2018-11-28
