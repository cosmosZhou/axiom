from util import *


@apply
def apply(given):
    (M, fx), *limits = given.of(All[LessEqual])
    assert not M.has(*(v for v, *_ in limits))
    return Inf(fx, *limits) >= M


@prove
def prove(Eq):
    from axiom import algebra

    M, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[x:a:b](M <= f(x)))

    Eq << Eq[0].this.expr.reversed

    Eq << algebra.all_ge.imply.inf_ge.apply(Eq[-1])

    


if __name__ == '__main__':
    run()
# created on 2019-01-24
# updated on 2023-04-14
