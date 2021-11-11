from util import *




@apply
def apply(given, n, start=0):
    start = sympify(start)

    fn, fn1 = given.of(Infer)

    assert fn._subs(n, n + 1) == fn1

    assert fn._subs(n, start).simplify()

    assert n.domain.min() >= start

    return fn


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True, nonnegative=True)

    k = Symbol(integer=True, positive=True)
    x = Symbol(integer=True, shape=(k,))
    i = Symbol(integer=True)

    w = Symbol(integer=True, shape=(oo, k, k))

    S = Symbol(etype=dtype.integer * k)

    Eq << apply(Infer(All[x:S](Element(x @ MatProduct[i:n](w[i]), S)), All[x:S](Element(x @ MatProduct[i:n + 1](w[i]), S))), n=n)

    Eq << Eq[0].lhs._subs(n, Zero()).copy(plausible=True)

    Eq << Eq[-1].simplify()

    Eq << algebra.cond.infer.imply.cond.induct.apply(Eq[-1], Eq[0], n=n)


if __name__ == '__main__':
    run()
# created on 2018-04-18
# updated on 2018-04-18
