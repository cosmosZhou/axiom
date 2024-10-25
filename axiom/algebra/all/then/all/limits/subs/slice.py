from util import *


@apply
def apply(given, old, new):
    function, (var, domain) = given.of(All)

    assert old.is_Sliced and old == var
    assert new.is_Sliced and new.base.is_symbol and new.base.is_given is None

    return All[new:domain](function._subs(old, new))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True, positive=True)

    a, b = Symbol(real=True)
    x = Symbol(real=True, shape=(oo,))
    f = Function(real=True, shape=())

    Eq << apply(All[x[:n]:CartesianSpace(Interval(a, b), n)](f(x[:n]) > 0), x[:n], x[1:n + 1])

    Eq << algebra.all.then.ou.subs.apply(Eq[0], x[:n], x[1:n + 1])

    Eq << algebra.all.of.ou.apply(Eq[1])


if __name__ == '__main__':
    run()

# created on 2018-12-16
