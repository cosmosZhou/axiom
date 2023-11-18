from util import *


@apply
def apply(given, x=None):
    S, n = given.of(Equal[Card])
    i = S.generate_var(integer=True)
    j = S.generate_var(integer=True, excludes={i})
    kwargs = S.etype.dict
    if 'shape' in kwargs:
        shape = (oo,) + kwargs['shape']
    else:
        shape = (oo,)
    kwargs.pop('shape', None)
    if x is None:
        x = S.generate_var(shape=shape, **kwargs)
    return Any[x[:n]:All[j:i, i:n](Unequal(x[i], x[j]))](Equal(S, Cup[i:n]({x[i]})))


@prove
def prove(Eq):
    from axiom import algebra, sets

    n = Symbol(domain=Range(2, oo), given=False)
    k = Symbol(integer=True, positive=True)
    S = Symbol(etype=dtype.integer[k])
    Eq << apply(Equal(Card(S), n))

    Eq << Infer(Eq[0], Eq[1], plausible=True)

    Eq.initial = Eq[-1].subs(n, 2)

    Eq << Eq.initial.this.rhs.doit(deep=True)

    Eq << Eq[-1].this.find(Sliced).apply(algebra.slice.to.block)

    Eq << Eq[-1].this.find(Unequal).reversed

    A = Eq[1].variable
    Eq << Eq[-1].this.lhs.apply(sets.eq_card.imply.any.eq.two, A[0], A[1])

    Eq.induct = Eq[2].subs(n, n + 1)

    Eq.size_deduction = Eq.induct.lhs.this.apply(sets.eq.imply.any.eq.size_deduction, var=A[n])

    Eq << algebra.cond.imply.cond.subs.apply(Eq[2], S, Eq.size_deduction.rhs.expr.lhs.arg)

    Eq << algebra.infer.imply.ou.apply(Eq[-1])

    Eq << algebra.ou.imply.any.ou.apply(Eq[-1])

    Eq << algebra.cond.infer.imply.infer.et.rhs.apply(Eq[-1], Eq.size_deduction)

    Eq << Eq[-1].this.rhs.apply(algebra.any.any.imply.any.et)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.et.imply.cond, index=1)

    Eq << Eq[-1].this.rhs.expr.apply(sets.eq.imply.eq.union_intersect, A[n].set)

    Eq << Eq[-1].this.find(Any).apply(algebra.any.imply.any.et.limits.unleash, 0, simplify=None)

    Eq << Eq[-1].this.find(Element).apply(sets.el.imply.eq.union)

    Eq << Eq[-1].this.find(And).args[-2:].apply(algebra.eq.cond.imply.cond.subs)

    Eq << Eq[-1].this.find(Equal[2]).apply(sets.intersect_is_empty.imply.notin, simplify=None)

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin.imply.all_notin)

    Eq << Eq[-1].this.rhs.apply(algebra.any_et.imply.any.limits_absorb, index=1)

    Eq << Eq[-1].this.rhs.apply(sets.any.imply.any.limits.swap)

    Eq << Eq[-1].this.rhs.expr.apply(sets.all_ne.all_ne.imply.all.ne)

    Eq << Eq[-1].this.rhs.apply(sets.any.imply.any.limits.swap)

    Eq << Infer(Eq[2], Eq.induct, plausible=True)

    Eq << algebra.cond.infer.imply.cond.induct.apply(Eq.initial, Eq[-1], start=2, n=n)

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq[2])



if __name__ == '__main__':
    run()

# created on 2020-09-10

from . import condset
# updated on 2023-11-11
from . import two
from . import real
