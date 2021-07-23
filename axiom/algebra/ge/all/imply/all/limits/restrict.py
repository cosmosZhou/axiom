from util import *


@apply
def apply(le, given):
    c, _a = le.of(GreaterEqual)
    function, (x, *ab) = given.of(All)
    if len(ab) == 2:
        a, b = ab        
        limit = (x, c, b)
    else:
        [ab] = ab
        a, b = ab.of(Interval)
        limit = (x, Interval(c, b, left_open=ab.left_open, right_open=ab.right_open))
        
    assert _a == a
    
    return All(function, limit)


@prove
def prove(Eq):
    from axiom import algebra

    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    c = Symbol.c(real=True, given=True)
    x = Symbol.x(real=True)
    f = Function.f(shape=(), real=True)
    Eq << apply(c >= a, All[x:a:b](f(x) > 0))

    e = Symbol.e(nonnegative=True)
    Eq << algebra.all.imply.all.limits.restrict.apply(Eq[1], Interval(a + e, b))

    Eq << algebra.cond.imply.suffice.unbounded.apply(Eq[-1], e)

    e = Eq[-1].lhs.lhs
    Eq << Eq[-1].subs(e, c - a)

    Eq << algebra.ge.imply.is_nonnegative.apply(Eq[0])

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()