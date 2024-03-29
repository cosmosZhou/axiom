from util import *


@apply
def apply(le, given):
    c, b = le.of(LessEqual)
    function, (x, *ab) = given.of(All)
    if len(ab) == 2:
        a, S[b] = ab
        limit = (x, a, c)
    else:
        ab, = ab
        a, S[b] = ab.of(Interval)
        limit = (x, Interval(a, c, **ab.kwargs))

    return All(function, limit)


@prove
def prove(Eq):
    from axiom import algebra

    a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    f = Function(shape=(), real=True)
    Eq << apply(c <= b, All[x:Interval(a, b)](f(x) > 0))

    e = Symbol(nonnegative=True)
    Eq << algebra.all.imply.all.limits.restrict.apply(Eq[1], Interval(a, b - e))

    Eq << algebra.cond.imply.infer.unbounded.apply(Eq[-1], e)

    e = Eq[-1].lhs.lhs
    Eq << Eq[-1].subs(e, b - c)

    Eq << algebra.le.imply.ge_zero.apply(Eq[0])

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2019-10-23
