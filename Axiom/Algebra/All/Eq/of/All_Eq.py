from util import *


@apply
def apply(given):
    function, (n, *ab) = given.of(All)
    assert n.is_integer
    if len(ab) == 2:
        a, S[oo] = ab
        assert a.is_integer and a.is_finite
    elif len(ab) == 1:
        domain = ab[0]
        assert domain.lhs == n
        if domain.is_GreaterEqual:
            a = domain.rhs
        elif domain.is_Greater:
            a = ceil(domain.rhs)
        else:
            return

    lhs, rhs = function.of(Equal)
    assert lhs == rhs._subs(n, n + 1)
    assert lhs.is_complex and rhs.is_complex
    return All[n:a:oo](Equal(rhs, rhs._subs(n, a)))


@prove
def prove(Eq):
    from Axiom import Algebra

    n, a = Symbol(integer=True)
    f = Function(complex=True)
    Eq << apply(All[n:a:oo](Equal(f(n + 1), f(n))))

    Eq << Eq[0].this.expr - Eq[0].rhs

    _n = Symbol("n", domain=Range(a, oo))
    Eq << Algebra.All.of.All.limits.restrict.apply(Eq[-1], Range(a, _n))

    Eq << Algebra.EqSum.of.All_Eq.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.doit()

    Eq << Algebra.All.of.Cond.apply(Eq[-1], _n)

    Eq << Eq[-1].this.apply(Algebra.All.limits.subs.offset, -1).reversed

    Eq << Algebra.All.given.And.All.apply(Eq[1], cond={a})




if __name__ == '__main__':
    run()
# created on 2019-01-07
# updated on 2023-06-24
