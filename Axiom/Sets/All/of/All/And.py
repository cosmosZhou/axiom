from util import *


@apply
def apply(given):
    function, (x, domain) = given.of(All)

    assert domain.is_set

    return All[x:domain](function & Unequal(domain, x.emptySet))


@prove
def prove(Eq):
    from Axiom import Algebra

    A = Symbol(etype=dtype.real, given=True)
    e = Symbol(real=True)
    f = Function(shape=(), integer=True)
    Eq << apply(All[e:A](f(e) > 0))

    Eq << Algebra.All_And.to.And.All.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2021-01-08