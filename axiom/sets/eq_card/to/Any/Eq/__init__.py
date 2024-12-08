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
    from Axiom import Algebra, Sets

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
    Eq << Eq[-1].this.lhs.apply(Sets.Eq_Card.to.Any.Eq.two, A[0], A[1])

    Eq.induct = Eq[2].subs(n, n + 1)

    Eq.size_deduction = Eq.induct.lhs.this.apply(Sets.Eq.to.Any.Eq.size_deduction, var=A[n])

    Eq << Algebra.Cond.to.Cond.subs.apply(Eq[2], S, Eq.size_deduction.rhs.expr.lhs.arg)

    Eq << Algebra.Imply.to.Or.apply(Eq[-1])

    Eq << Algebra.Or.to.Any.Or.apply(Eq[-1])

    Eq << Algebra.Cond.Imply.to.Imply.And.rhs.apply(Eq[-1], Eq.size_deduction)

    Eq << Eq[-1].this.rhs.apply(Algebra.Any.Any.to.Any.And)

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.And.to.Cond, index=1)

    Eq << Eq[-1].this.rhs.expr.apply(Sets.Eq.to.Eq.union_Intersect, A[n].set)

    Eq << Eq[-1].this.find(Any).apply(Algebra.Any.to.Any.And.limits.unleash, 0, simplify=None)

    Eq << Eq[-1].this.find(Element).apply(Sets.In.to.Eq.Union)

    Eq << Eq[-1].this.find(And).args[-2:].apply(Algebra.Eq.Cond.to.Cond.subs)

    Eq << Eq[-1].this.find(Equal[2]).apply(Sets.Intersect_Eq_EmptySet.to.NotIn, simplify=None)

    Eq << Eq[-1].this.find(NotElement).apply(Sets.NotIn.to.All_NotIn)

    Eq << Eq[-1].this.rhs.apply(Algebra.Any_And.to.Any.limits_absorb, index=1)

    Eq << Eq[-1].this.rhs.apply(Sets.Any.to.Any.limits.swap)

    Eq << Eq[-1].this.rhs.expr.apply(Sets.All_Ne.All_Ne.to.All.Ne)

    Eq << Eq[-1].this.rhs.apply(Sets.Any.to.Any.limits.swap)

    Eq << Imply(Eq[2], Eq.induct, plausible=True)

    Eq << Algebra.Cond.Imply.to.Cond.induct.apply(Eq.initial, Eq[-1], start=2, n=n)

    Eq << Algebra.Cond.Imply.to.Cond.trans.apply(Eq[0], Eq[2])



if __name__ == '__main__':
    run()

# created on 2020-09-10

# updated on 2023-11-11


from . import Condset
from . import two
from . import real
