from util import *


@apply
def apply(le, given):
    c, a = le.of(GreaterEqual)
    function, (x, *ab) = given.of(All)
    if len(ab) == 2:
        S[a], b = ab
        limit = (x, c, b)
    else:
        ab, = ab
        S[a], b = ab.of(Interval)
        limit = (x, Interval(c, b, **ab.kwargs))

    return All(function, limit)


@prove
def prove(Eq):
    from axiom import algebra

    a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    f = Function(shape=(), real=True)
    Eq << apply(c >= a, All[x:Interval(a,b)](f(x) > 0))

    e = Symbol(nonnegative=True)
    Eq << algebra.all.then.all.limits.restrict.apply(Eq[1], Interval(a + e, b))

    Eq << algebra.cond.then.infer.unbounded.apply(Eq[-1], e)

    e = Eq[-1].lhs.lhs
    Eq << Eq[-1].subs(e, c - a)

    Eq << algebra.ge.then.ge_zero.apply(Eq[0])

    Eq << algebra.cond.infer.then.cond.trans.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2019-05-15
