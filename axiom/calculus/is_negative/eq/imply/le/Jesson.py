from util import *


@apply
def apply(is_positive, eq, x=None):
    fx, (x_, d) = is_positive.of(Derivative < 0)
    assert d == 2

    wi, (i, n) = eq.of(Equal[Sum[Tuple[0, Expr]], 1])
    assert wi >= 0

    domain = x_.domain
    assert domain.left_open and domain.right_open
    if x is None:
        x = Symbol.x(shape=(oo,), domain=domain)
    assert x.domain_assumed == domain
    return LessEqual(Sum[i:n](wi * fx._subs(x_, x[i])), fx._subs(x_, Sum[i:n](wi * x[i])))


@prove
def prove(Eq):
    from axiom import calculus, algebra

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    a, b = Symbol(real=True)
    x = Symbol(domain=Interval(a, b, left_open=True, right_open=True))
    w = Symbol(shape=(oo,), nonnegative=True)
    f = Function(real=True)
    Eq << apply(Derivative(f(x), (x, 2)) < 0, Equal(Sum[i:n](w[i]), 1))

    Eq << -Eq[0]

    Eq << Eq[-1].this.lhs.apply(calculus.mul.to.derivative)

    Eq << calculus.is_positive.eq.imply.ge.Jesson.apply(Eq[-1], Eq[1])

    Eq << -Eq[-1]

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.sum)


if __name__ == '__main__':
    run()
