from util import *


@apply
def apply(set_comprehension_equality, last_element_equality):
    from axiom.sets.eq.given.eq.set_comprehension import of_set_comprehension
    if last_element_equality.lhs.is_Cup:
        last_element_equality, set_comprehension_equality = set_comprehension_equality, last_element_equality

    p, n = last_element_equality.lhs.of(Indexed)
    _n = last_element_equality.rhs
    assert _n == n

    set_comprehension, interval = set_comprehension_equality.of(Equal)
    _p = of_set_comprehension(set_comprehension)
    assert p[:n + 1] == _p
    assert interval == Range(0, n + 1)

    return Equal(p[:n].set_comprehension(), Range(0, n))


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol.n(integer=True, positive=True, given=True)
    p = Symbol.p(shape=(oo,), integer=True, nonnegative=True, given=True)
    Eq << apply(Equal(p[:n + 1].set_comprehension(), Range(0, n + 1)),
                Equal(p[n], n))

    Eq << Eq[0].this.lhs.apply(sets.cup.to.union.split, cond=slice(-1))

    Eq << Eq[-1].subs(Eq[1])

    Eq << sets.eq.imply.eq.complement.apply(Eq[-1], {n})

    Eq << Eq[2].subs(Eq[-1].reversed).reversed

    Eq.plausible = NotContains(n, Eq[-1].rhs, plausible=True)

    Eq << ~Eq.plausible

    Eq << Eq[-1].apply(sets.contains.imply.any_contains.st.cup)

    i = Eq[-1].variable
    _i = i.copy(domain=Range(0, n))
    Eq << Eq[-1].limits_subs(i, _i)

    Eq << Eq[0].lhs.this.apply(sets.cup.to.union.split, cond={_i, n})

    Eq << Eq[-1].this.rhs.args[0].apply(sets.cup.to.union.doit.setlimit, evaluate=False)

    Eq << algebra.any_eq.cond.imply.any.subs.apply(Eq[-3].reversed, Eq[-1])

    Eq.paradox = Eq[-1].subs(Eq[1])

    Eq << sets.imply.le.union.apply(*Eq.paradox.expr.rhs.args)

    Eq << sets.imply.le.cup.apply(*Eq.paradox.expr.rhs.args[1].args)

    Eq << Eq[-2] + Eq[-1]

    Eq << Eq[-1].this.apply(algebra.le.simplify.terms.common)

    Eq << Eq.paradox.this.expr.apply(algebra.eq.imply.eq.abs)

    Eq << Eq[-1].subs(Eq[0])

    Eq << algebra.any_eq.cond.imply.any.subs.apply(Eq[-1].reversed, Eq[-3])

    Eq << sets.notcontains.imply.eq.complement.apply(Eq.plausible)


if __name__ == '__main__':
    run()