from util import *



@apply
def apply(f0, f1, suffice, n=None, start=0):
    start = sympify(start)
    fn_fn1, fn2 = suffice.of(Infer)
    fn, fn1 = fn_fn1.of(And)

    if fn._subs(n, n + 1) != fn1:
        fn, fn1 = fn1, fn

    assert fn._subs(n, n + 1) == fn1
    assert fn._subs(n, n + 2) == fn2

    assert fn._subs(n, start) == f0
    assert fn._subs(n, start + 1) == f1
    assert n.domain.min() == start

    return fn


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    f, g = Symbol(integer=True, shape=(oo,))
    Eq << apply(f[1] < g[1], f[2] < g[2], Infer((f[n] < g[n]) & (f[n + 1] < g[n + 1]), f[n + 2] < g[n + 2]), n=n, start=1)

    Eq << Infer((f[n] < g[n]) & (f[n + 1] < g[n + 1]), f[n + 1] < g[n + 1], plausible=True)

    Eq << algebra.infer.infer.imply.infer.et.apply(Eq[-1], Eq[2], simplify=None)

    Eq <<= Eq[0] & Eq[1]

    Eq << algebra.cond.infer.imply.cond.induct.apply(Eq[-1], Eq[-2], n=n, start=1)

    Eq << algebra.et.imply.cond.apply(Eq[-1], index=0)

    


if __name__ == '__main__':
    run()

# created on 2019-03-14
# updated on 2023-05-20
