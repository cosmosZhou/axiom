from util import *



@apply
def apply(given, n=None, start=0):
    start = sympify(start)
    fn, fn1 = given.of(Infer)
    assert fn._subs(n, n + 1) == fn1

    assert fn._subs(n, start)
    assert n.domain.min() >= start

    return fn


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True, nonnegative=True)
    f, h = Symbol(integer=True, shape=(oo,))
    g = Lamda[n](Piecewise((f[0], Equal(n, 0)), (h[n], True)))

    Eq << apply(Infer(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])), n=n)

    g = Symbol(Lamda[n](Piecewise((f[0], Equal(n, 0)), (h[n], True))))
    Eq.equality = g[0].this.definition.reversed

    Eq.suffice = Infer(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1]), plausible=True)

    Eq << Eq.suffice.this.lhs.rhs.definition

    Eq << Eq[-1].this.rhs.rhs.definition

    Eq << algebra.cond.infer.imply.cond.induct.apply(Eq.equality, Eq.suffice, n=n)

    Eq << Eq[-1].this.rhs.definition


if __name__ == '__main__':
    run()
# created on 2018-08-20
# updated on 2018-08-20
