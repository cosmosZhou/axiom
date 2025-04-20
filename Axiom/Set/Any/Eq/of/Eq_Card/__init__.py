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
    from Axiom import Algebra, Set, Logic

    n = Symbol(domain=Range(2, oo), given=False)
    k = Symbol(integer=True, positive=True)
    S = Symbol(etype=dtype.integer[k])
    Eq << apply(Equal(Card(S), n))

    Eq << Imply(Eq[0], Eq[1], plausible=True)

    Eq.initial = Eq[-1].subs(n, 2)

    Eq << Eq.initial.this.rhs.doit(deep=True)

    Eq << Eq[-1].this.find(Sliced).apply(Algebra.Slice.eq.Block)

    Eq << Eq[-1].this.find(Unequal).reversed

    A = Eq[1].variable
    Eq << Eq[-1].this.lhs.apply(Set.Any.Eq.of.Eq_Card.two, A[0], A[1])

    Eq.induct = Eq[2].subs(n, n + 1)

    Eq.size_deduction = Eq.induct.lhs.this.apply(Set.Any.Eq.of.Eq.size_deduction, var=A[n])

    Eq << Algebra.Cond.of.Cond.subs.apply(Eq[2], S, Eq.size_deduction.rhs.expr.lhs.arg)

    Eq << Logic.Or.of.ImpNot.apply(Eq[-1])

    Eq << Algebra.Any.Or.of.Or.apply(Eq[-1])

    Eq << Logic.Imp.And.of.Cond.Imp.rhs.apply(Eq[-1], Eq.size_deduction)

    Eq << Eq[-1].this.rhs.apply(Algebra.Any.And.of.Any.Any)

    Eq << Eq[-1].this.rhs.expr.apply(Logic.Cond.of.And, index=1)

    Eq << Eq[-1].this.rhs.expr.apply(Set.Eq.of.Eq.union_Inter, A[n].set)

    Eq << Eq[-1].this.find(Any).apply(Algebra.Any.And.of.Any.limits.unleash, 0, simplify=None)

    Eq << Eq[-1].this.find(Element).apply(Set.EqUnion.of.Mem)

    Eq << Eq[-1].this.find(And).args[-2:].apply(Logic.Cond.of.Eq.Cond.subs)

    Eq << Eq[-1].this.find(Equal[2]).apply(Set.NotMem.of.Inter_Eq_EmptySet, simplify=None)

    Eq << Eq[-1].this.find(NotElement).apply(Set.All_NotMem.of.NotMem)

    Eq << Eq[-1].this.rhs.apply(Algebra.Any.of.Any_And.limits_absorb, index=1)

    Eq << Eq[-1].this.rhs.apply(Set.Any.of.Any.limits.swap)

    Eq << Eq[-1].this.rhs.expr.apply(Set.All.Ne.of.All_Ne.All_Ne)

    Eq << Eq[-1].this.rhs.apply(Set.Any.of.Any.limits.swap)

    Eq << Imply(Eq[2], Eq.induct, plausible=True)

    Eq << Logic.Cond.of.Cond.Imp.induct.apply(Eq.initial, Eq[-1], start=2, n=n)

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[0], Eq[2])



if __name__ == '__main__':
    run()

# created on 2020-09-10

# updated on 2023-11-11


from . import real
from . import two
