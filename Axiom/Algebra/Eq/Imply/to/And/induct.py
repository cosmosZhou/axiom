from util import *


@apply
def apply(f0, suffice, n=None, x=None, start=0):
    start = sympify(start)
    f0.of(Equal)
    fn_and_fnt, fn1 = suffice.of(Imply)

    fn, fnt = fn_and_fnt.of(And)

    if fn1._subs(n, n - 1) == fnt:
        fn, fnt = fnt, fn

    assert fn1._subs(n, n - 1) == fn

    assert fn._subs(x, x + 1) == fnt
    assert fn._subs(n, start) == f0

    assert n.domain.min() == start

    return fn, fnt


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True, nonnegative=True)
    f, g = Function(shape=(), real=True)
    x = Symbol(real=True)
    Eq << apply(Equal(f[0](x), g[0](x)), Imply(Equal(f[n](x), g[n](x)) & Equal(f[n](x + 1), g[n](x + 1)), Equal(f[n + 1](x), g[n + 1](x))), n=n, x=x)

    Eq << Imply(Eq[2], Eq[2]._subs(x, x + 1), plausible=True)

    Eq << Eq[-1].this.lhs.apply(Algebra.Cond.to.Cond.subs, x, x + 1)

    Eq << Algebra.Imply_And.to.Imply.And.apply(Eq[-1])

    Eq << Algebra.Imply.Imply.to.Imply.trans.apply(Eq[-1], Eq[1])

    Eq << Algebra.Cond.Imply.to.Cond.induct.apply(Eq[0], Eq[-1], n=n)

    Eq << Eq[2].subs(x, x + 1)




if __name__ == '__main__':
    run()
# created on 2019-04-17
# updated on 2023-05-21