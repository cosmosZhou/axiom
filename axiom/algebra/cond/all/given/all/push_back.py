from util import *


@apply
def apply(cond, all):
    fn, (k, a, b) = all.of(All)

    assert k.is_integer
    assert fn._subs(k, b) == cond
    return All[k:a:b + 1](fn)


@prove
def prove(Eq):
    from axiom import algebra

    k, a = Symbol(integer=True)
    b = Symbol(domain=Range(a + 1, oo))
    g = Function(integer=True)
    Eq << apply(g(b) > 0, All[k:a:b](g(k) > 0))

    Eq << algebra.all.imply.et.split.apply(Eq[-1], cond={b})


if __name__ == '__main__':
    run()
# created on 2018-04-01
# updated on 2018-04-01
