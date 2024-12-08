from util import *


@apply
def apply(a_size, xa_equality, j=None):
    x_cup_finiteset, a_cup_finiteset = xa_equality.of(Equal)
    xexpr, (k, a, b) = x_cup_finiteset.of(Cup[FiniteSet])
    S[a_cup_finiteset], n = a_size.of(Equal[Card])

    assert n == b - a

    aexpr, (_k, _a, _b) = a_cup_finiteset.of(Cup[FiniteSet])
    assert n == _b - _a

    x = Lamda[k:a:b](xexpr).simplify()
    a = Lamda[_k:_a:_b](aexpr).simplify()

    if j is None:
        j = Symbol(domain=Range(n), given=True)

    assert 0 <= j < n

    from Axiom.Discrete.Eq.to.And.index import index_function
    index = index_function(n)
    index_j = index[j](x[:n], a[:n], evaluate=False)
    return Element(index_j, Range(n)), Equal(x[index_j], a[j])


@prove
def prove(Eq):
    from Axiom import Discrete, Algebra, Sets

    n = Symbol(domain=Range(2, oo), given=True)
    x, a = Symbol(shape=(n,), integer=True, given=True)
    k = Symbol(integer=True)
    j = Symbol(domain=Range(n), given=True)
    Eq << apply(Equal(Card(a.cup_finiteset(k)), n),
                Equal(x[:n].cup_finiteset(k), a.cup_finiteset(k)),
                j=j)

    Eq << Eq[2].lhs.this.defun()

    Eq <<= Eq[-3].subs(Eq[-1]), Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].lhs.indices[0].this.apply(Discrete.Dot.eq.Sum)

    Eq << Eq[-1].rhs.expr.args[1].this.apply(Algebra.Delta.eq.Piece)

    Eq << Algebra.Eq.Eq.to.Eq.subs.rhs.apply(Eq[-1], Eq[-2])

    s_j = Symbol(conditionset(k, Equal(a[j], x[k]), Range(n)))
    Eq.s_j_definition = s_j.this.definition

    Eq << Sum[k:s_j](k).this.limits[0][1].definition

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Add.split, cond={0})

    Eq.crossproduct = Algebra.Eq.Eq.to.Eq.trans.apply(Eq[-3], Eq[-1])

    Eq.s_j_definition_reversed = Eq.s_j_definition.this.rhs.limits[0][1].reversed.reversed

    Eq << Eq[1].apply(Sets.Eq.to.Eq.Intersect, {a[j]})

    k_ = Eq[-1].find(Cup).variable
    Eq << Piecewise((x[k_].set, Equal(x[k_], a[j])), (x[k_].emptySet, True)).this.simplify()

    Eq << Sets.Eq.to.Eq.Cup.apply(Eq[-1].reversed, (k_, 0, n))

    Eq.distribute = Eq[-1].subs(Eq[-3]).reversed

    Eq << Eq.distribute.this.lhs.apply(Sets.Imageset.inner_subs)

    Eq << Eq[-1].subs(Eq.s_j_definition_reversed)

    Eq.s_j_greater_than_1 = Sets.Ne_EmptySet.to.Ge.apply(Eq[-1])

    Eq.distribute = Eq.distribute.subs(Eq.s_j_definition_reversed)

    Eq.ou = Sets.Le_.Card.One.ou.Any_Ne.apply(Eq.s_j_greater_than_1.lhs.arg)

    Eq.s_j_less_than_1 = Eq.ou.args[0].copy(plausible=True)

    Eq.inequality_ab = Eq.ou.args[1].copy(plausible=True)

    (a, *_), (b, *_) = Eq.inequality_ab.limits
    Eq << Eq[1].apply(Sets.Eq.to.Eq.Card)

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq[-1], Eq[0])

    Eq << Sets.Eq.to.All.Ne.Complement.apply(Eq[-1], exclude=a)

    Eq << Eq[-1].subs(k_, a)

    Eq << Algebra.All.to.Or.subs.apply(Eq[-1], Eq[-1].variable, b)

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[-1], Eq.inequality_ab)

    Eq.distribute_ab = Eq[-1].this.expr.apply(Algebra.And.to.Or)

    Eq.j_equality = Sets.All_Eq_.CupFiniteSet.Range.apply(s_j)

    Eq << Eq.j_equality.limits_subs(k, a)

    Eq << Algebra.All.Any.to.Any.And.apply(Eq.j_equality.reversed, Eq.distribute_ab)

    Eq << Eq[-1].this.expr.args[::2].apply(Algebra.Eq.Cond.to.Cond.subs, ret=0)

    Eq << Eq[-1].this.expr.apply(Algebra.And.to.And.delete)

    Eq << Eq.j_equality.limits_subs(a, b)

    Eq << Algebra.All.Any.to.Any.And.apply(Eq.j_equality, Eq[-1])

    Eq <<= Eq.ou & ~Eq.inequality_ab

    Eq << Algebra.And.to.Cond.apply(Eq[-1], index=0)

    Eq <<= Eq.s_j_less_than_1 & Eq.s_j_greater_than_1

    Eq << Sets.Eq.to.In.Sum.apply(Eq[-1], var=k)

    Eq.index_domain = Eq[-1].subs(Eq.crossproduct.reversed)

    Eq.ou = Algebra.All.to.Or.subs.apply(Eq.j_equality, Eq.j_equality.variable, Eq.index_domain.lhs)

    Eq <<= Eq.ou.args[1].copy(plausible=True), Eq.ou.args[0].copy(plausible=True)

    Eq <<= Eq[-2] & Eq.index_domain

    Eq <<= Eq.ou & ~Eq[-2]

    Eq << Algebra.And.to.Cond.apply(Eq[-1], index=0)

    Eq << Eq[-2].reversed

    Eq << Subset(s_j, Eq[2].rhs, plausible=True)

    Eq << Sets.In.Subset.to.In.apply(Eq.index_domain, Eq[-1])





if __name__ == '__main__':
    run()

# https://docs.sympy.org/latest/modules/combinatorics/permutations.html

# created on 2020-07-22
# updated on 2023-11-11

