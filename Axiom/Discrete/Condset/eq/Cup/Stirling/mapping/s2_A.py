from util import *


@apply
def apply(n, k, s2=None, A=None):
    from sympy.functions.combinatorial.numbers import Stirling
    j = Symbol(domain=Range(k + 1))
    if s2 is None:
        x = Symbol(shape=(oo,), etype=dtype.integer, finiteset=True)
        s2 = Symbol(Cup[x[:k + 1]:Stirling.conditionset(n + 1, k + 1, x)](x[:k + 1].cup_finiteset().set))

    e = Symbol(**s2.etype.dict)
    if A is None:
        x = s2.definition.variable.base
        i = Symbol(integer=True)
        s1_quote = Symbol("s'_1", Stirling.conditionset(n, k + 1, x))
        x_quote = Symbol(Lamda[i:k + 1](Piecewise(({n} | x[i], Equal(i, j)), (x[i], True))))
        A = Symbol(Lamda[j](Cup[x[:k + 1]:s1_quote]({x_quote.cup_finiteset()})))

    return Equal(conditionset(e, NotElement({n}, e), s2), Cup[j](A[j]))


@prove(proved=False)
def prove(Eq):
    from Axiom import Sets, Algebra

    k = Symbol(integer=True, positive=True)
    n = Symbol(integer=True, positive=True, given=True)
    Eq << apply(n, k)

    s2_quote = Symbol('s_quote_2', conditionset(Eq[0].rhs.variable, Eq[0].rhs.limits[0][1]))
    Eq << s2_quote.this.definition

    Eq.s2_definition = imageset(Eq[0].rhs.variable, Eq[0].rhs.expr.arg, s2_quote).this.subs(Eq[-1]).subs(Eq[0].reversed).reversed

    s1_quote = Eq[2].lhs
    Eq << Sets.All_Eq_.CupFiniteSet.Range.apply(s1_quote)

    i = Eq[1].lhs.indices[0]
    x_slice = Eq[-1].limits[0][0]
    x = x_slice.base
    Eq.x_abs_positive_s1 = Algebra.All_And.to.All.apply(Eq[-1])

    Eq.x_abs_sum_s1 = Algebra.All_And.to.All.apply(Eq[-1], 1)

    Eq.x_union_s1 = Algebra.All_And.to.All.apply(Eq[-1], 2)

    j = Symbol(domain=Range(k + 1))
    x_quote = Eq[1].lhs.base
    Eq.x_quote_set_in_s2 = Subset(imageset(x_slice, Cup[i:k + 1](x_quote[i].set), s1_quote), Eq[0].lhs, plausible=True)

    Eq << Sets.Subset.of.All_In.apply(Eq.x_quote_set_in_s2)

    Eq << Eq[-1].subs(Eq.s2_definition)

    Eq << Eq[-1].this.expr.apply(Sets.In.of.In.split.Imageset)

    Eq << Eq[-1].this.expr.rhs.definition

    Eq << Eq[-1].this.expr.args[0].simplify()

    Eq << Sets.Eq.to.Eq.Cup.apply(Eq[1], (i, 0, k + 1))

    Eq.x_quote_union = Algebra.All_Eq.Cond.to.All.subs.apply(Eq.x_union_s1, Eq[-1])

    Eq << Eq[1].apply(Sets.Eq.to.Eq.Card)

    x_quote_abs = Eq[-1]
    Eq << Eq[-1].apply(Algebra.Eq.to.Eq.Sum, (i, 0, k + 1))

    Eq << Sets.CardUnion.le.AddCardS.apply(*Eq[-1].rhs.args[1].arg.args)

    Eq << Algebra.Eq.Le.to.Le.subs.apply(Eq[-2], Eq[-1])

    Eq << Algebra.All_Eq.Cond.to.All.subs.apply(Eq.x_abs_sum_s1, Eq[-1])

    Eq << Eq.x_quote_union.this.expr.apply(Sets.Eq.to.Eq.Card)

    x_quote_union_abs = Eq[-1]
    u = Eq[-1].lhs.arg
    Eq << Sets.CardCup.le.Sum_Card.apply(u.expr, *u.limits)

    Eq << Eq[-2].this.expr.apply(Algebra.Eq.Le.to.Ge.subs, Eq[-1])

    Eq.SqueezeTheorem = Eq[-4] & Eq[-1]

    Eq << Algebra.Cond_Piece.to.Or.apply(x_quote_abs)

    Eq << Eq[-1].subs(i, j)

    Eq << Eq[-2].apply(Algebra.Cond.to.All.restrict, (i, Unequal(i, j)))

    Eq << Sets.CardUnion.ge.Card.apply(*Eq[-2].rhs.arg.args[::-1])

    Eq << Eq.x_abs_positive_s1.limits_subs(i, j).this.expr.apply(Algebra.Gt.Ge.to.Gt.trans, Eq[-1])

    Eq.xj_is_positive = Eq[-1].subs(Eq[-4].reversed)

    Eq << Algebra.All.All.to.All.And.apply(Eq.x_abs_positive_s1, Eq[-3].reversed)

    Eq.xi_is_positive = Eq[-1].this.expr.apply(Algebra.Eq.Cond.to.Cond.trans)

    Eq.xi_all_is_positive = Eq.xi_is_positive.apply(Algebra.All.of.All.limits.delete, index=0)

    Eq << Eq.xi_all_is_positive.this.expr.apply(Algebra.Cond.of.And.All, cond=Equal(i, j))

    Eq << Algebra.All_And.of.And.All.apply(Eq[-1])

    Eq << Eq[-1].apply(Algebra.All.of.All.Or.limits.delete, simplify=None)

    Eq << Eq[-1].this.find(NotElement).apply(Sets.NotIn_Complement.of.Or, simplify=None)

    Eq << Eq[-1].this.find(Greater).apply(Algebra.Cond.of.Or.domain_defined, wrt=i, simplify=None)

    Eq << Eq.xi_is_positive.apply(Algebra.All.to.All.Or.limits.delete, simplify=None)

    Eq << Eq[-1].this.find(NotElement).apply(Sets.NotIn_Complement.to.Or, simplify=None)

    Eq <<= Eq.x_quote_union & Eq.SqueezeTheorem & Eq.xi_all_is_positive

    Eq.x_quote_definition = Eq[1].apply(Algebra.Eq.to.Eq.Lamda, (i, 0, k + 1), simplify=False)

    Eq.subset_A = Subset(Eq[4].lhs, Eq[4].rhs, plausible=True)

    Eq.supset_A = Supset(Eq[4].lhs, Eq[3].lhs, plausible=True)

    Eq << Eq.supset_A.subs(Eq[3])

    Eq << Sets.Supset.of.All_In.apply(Eq[-1])

    Eq << Eq[-1].this.expr.simplify()

    Eq << Algebra.All_And.of.And.All.apply(Eq[-1])

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.expr.apply(Sets.In_Cup.to.Any_In)

    Eq << Eq.x_quote_definition[j]

    Eq << Eq[-2].reversed.this.expr.apply(Sets.Eq.Eq.to.Eq.Intersect, Eq[-1])

    Eq << Sets.CardUnion.eq.Sub_.AddCards.CardIntersect.principle.inclusion_exclusion.apply(*Eq[-1].lhs.args)

    Eq << Algebra.Any_Eq.Cond.to.Any.subs.apply(Eq[-2], Eq[-1])

    Eq.set_size_inequality = Eq[-1].this.expr.apply(Algebra.Eq.Lt.to.Lt.subs, Less(Eq[-1].expr.rhs, Eq[-1].expr.rhs + 1, plausible=True))

    Eq << Eq.x_quote_union.this.expr.lhs.apply(Sets.Cup.eq.Union.split, cond={i, j})

    Eq << Sets.CardUnion.le.AddCardS.apply(*Eq[-1].lhs.args)

    Eq << Sets.CardCup.le.Sum_Card.apply(*Eq[-2].lhs.args[0].args)

    Eq << Algebra.Le.Le.to.Le.subs.apply(Eq[-2], Eq[-1])

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[-1], Eq.set_size_inequality)

    Eq << Eq[-1].this.expr.apply(Algebra.Lt.Le.to.Lt.Add)

    return
    Eq << Eq[-1].this(var=Eq[-1].variables[0]).find(Sum).simplify()
    Eq << Eq[-1].this(var=Eq[-1].variables[0]).expr.rhs.find(Cup).simplify()
    Eq << Algebra.All.any.then.Any_And.apply(x_quote_union_abs, Eq[-1])
    Eq << Eq[-1].this.expr.apply(Algebra.eq.Cond.then.Cond.subs)
    Eq << Algebra.All.any.then.Any_And.apply(Eq.SqueezeTheorem, Eq[-1])
    Eq << Eq.subset_A.subs(Eq[3])
    Eq << Sets.Subset.of.All_In.apply(Eq[-1])
    s2_hat_n = Symbol("\hat{s}_{2, n}", conditionset(*Eq[-1].limits[0]))
    Eq << Sets.all.of.all.conditionset.split.baseset.apply(Eq[-1], simplify=False, s=s2_hat_n)
    Eq.s2_hat_n_assertion = Eq[-1].this.expr.apply(Sets.element.of.any_contains.split.cup)
    Eq << s2_hat_n.this.definition
    Eq << Eq[-1].this.rhs.apply(Sets.conditionset.to.imageset)
    s2_quote_n = Symbol("s'_{2, n}", conditionset(Eq[-1].rhs.variable, Eq[-1].rhs.limits[0][1]))
    assert s2_quote_n in s2_quote
    assert Supset(s2_quote, s2_quote_n)
    Eq << s2_quote_n.this.definition
    Eq << imageset(Eq[-2].rhs.variable, Eq[-2].rhs.expr.arg, s2_quote_n).this.subs(Eq[-1]).subs(Eq[-2].reversed).reversed
    Eq.s2_hat_n_hypothesis = Eq.s2_hat_n_assertion.this.limits[0].subs(Eq[-1])
    Eq << Sets.All_Eq_.CupFiniteSet.Range.apply(s2_quote_n)
    Eq << Eq[-1].this.expr.apply(Sets.Eq.Eq.All_is_positive.notcontains.then.eq.Stirling2, s1=s1_quote)
    Eq << Algebra.All_any.then.All_any.limits_swap.apply(Eq[-1])
    Eq << Eq.s2_hat_n_hypothesis.this.expr.expr.apply(Sets.eq.of.eq.cup_finiteset)
    Eq << Eq[-1].subs(Eq.x_quote_definition)
    Eq.supset_A = Sets.supset.then.supset.cup.lhs.apply(Eq.supset_A, (j,), simplify=False)
    Eq <<= Eq.supset_A & Eq.subset_A


if __name__ == '__main__':
    run()

# created on 2020-10-03
