from util import *


@apply
def apply(given):
    ((fx, m), *limits), (S[m], S[-oo], M0) = given.of(All[Any[Greater]])
    return Sup(fx, *limits) >= M0


@prove
def prove(Eq):
    from axiom import algebra

    M0, a, b = Symbol(real=True, given=True)
    M, x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[M:-oo:M0](Any[x:Interval(a, b)](f(x) > M)))

    Eq << ~Eq[1]

    Eq << algebra.sup_lt.imply.any.all.le.apply(Eq[-1])

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2018-12-30
