from util import *


@apply
def apply(given, old, new):
    expr, (n, a, b) = given.of(All[Tuple])
    assert n.is_integer
    assert old == n
    m = new + n + 1
    assert not m._has(n)
    # assert m == a + b
    return All[n:m - b:m - a](expr._subs(old, new))


@prove
def prove(Eq):
    from axiom import algebra, sets

    n, m = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(All[n:m + 1](f(n) > 0), n, m - n)

    Eq << algebra.all.then.ou.subs.apply(Eq[0], n, m - n)

    Eq << Eq[-1].this.args[1].apply(sets.notin.then.notin.neg)

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin.then.notin.add, m)

    Eq << algebra.ou.then.all.apply(Eq[-1], pivot=1, wrt=n)




if __name__ == '__main__':
    run()


# created on 2018-06-20
# updated on 2023-05-12
