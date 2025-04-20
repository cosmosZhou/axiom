from util import *


@apply
def apply(given):
    (xi, xj), *limits = given.of(All[Equal[Intersection, EmptySet]])

    if len(limits) == 2:
        (j, j_domain), i_limit = limits
        _, i = j_domain.of(Complement)
        i = i.of(FiniteSet)
    else:
        (i, j_domain), = limits
        universe, j = j_domain.of(Complement)
        j = j.of(FiniteSet)

        i_limit = (i, universe)

    if not xi._has(i):
        xi, xj = xj, xi

    assert xi._subs(i, j) == xj
    return Equal(Card(Cup(xi, i_limit).simplify()), Sum(Card(xi), i_limit))


@prove
def prove(Eq):
    from Axiom import Algebra, Set, Logic

    i, j = Symbol(integer=True)
    n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(oo,), etype=dtype.integer, finiteset=True)
    j_domain = Range(n) - {i}
    emptySet = x[i].etype.emptySet
    Eq << apply(All[j: j_domain, i: n](Equal(x[i] & x[j], emptySet)))

    y = Symbol(Lamda[i](Piecewise((x[i], i < n), (emptySet, True))))
    Eq.y_definition = y[i].this.definition

    Eq << Eq.y_definition.apply(Algebra.All.of.Cond.restrict, (i, 0, n))

    Eq.yi_definition = Eq[-1].this().expr.rhs.simplify()

    Eq << Eq.yi_definition.reversed

    Eq << Algebra.All.And.of.All.All.apply(Eq[0], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(Logic.Cond.of.Eq.Cond.subs)

    Eq << Algebra.All.And.of.All.All.apply(Eq[-1], Eq[-3].limits_subs(i, j), simplify=None)

    Eq.nonoverlapping = Eq[-1].this.expr.apply(Algebra.Eq.of.Eq.Eq.subs)

    Eq << Eq.y_definition.apply(Algebra.All.of.Cond.restrict, (i, n, oo))

    Eq << Eq[-1].this().expr.rhs.simplify()

    Eq << Eq[-1].this.expr.apply(Set.EqInter.of.Eq, y[j])

    Eq << Eq[-1].apply(Algebra.All.of.Cond.restrict, (j, j_domain))

    Eq <<= Eq[-1] & Eq.nonoverlapping

    Eq << Set.Eq.of.All_Eq_EmptySet.nonoverlapping.setlimit.utility.apply(Eq[-1])

    Eq << Algebra.All.of.All_Eq.Cond.subs.apply(Eq.yi_definition, Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-01-13


from . import utility
