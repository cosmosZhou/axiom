from util import *


@apply
def apply(given):
    (M, fx), *limits = given.of(All[GreaterEqual])
    return Sup(fx, *limits) <= M


@prove
def prove(Eq):
    from axiom import algebra

    M, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[x:a:b](M >= f(x)))

    Eq << Eq[0].this.expr.reversed

    Eq << algebra.all_le.imply.sup_le.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-01-18
