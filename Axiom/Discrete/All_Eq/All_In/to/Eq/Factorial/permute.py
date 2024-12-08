from util import *


@apply
def apply(all0, all1):

    (ref, s), (j, S[1], n_munis_1), (x, S[s]) = all0.of(All[Element])

    piecewise, (i, S[0], S[n_munis_1]) = ref.of(Lamda)
    assert s.is_set
    dtype = s.etype

    (x0, condition0), (xj, conditionj), (xi, S[True]) = piecewise.of(Piecewise)
    S[i] = condition0.of(Equal[j])
    S[i] = conditionj.of(Equal[0])

    n = n_munis_1

    assert x[j] == xj and x[i] == xi and x[0] == x0 and dtype == x.type

    equality, (S[x], S[s]) = all1.of(All)
    S[Card(x.cup_finiteset())] = equality.of(Equal[n])

    return Equal(Card(s), factorial(n) * Card(Cup[x:s]({x.cup_finiteset()})))


@prove(proved=False)
def prove(Eq):
    from Axiom import Discrete, Algebra, Sets

    n = Symbol(domain=Range(2, oo))
    S = Symbol(etype=dtype.integer[n])
    x = Symbol(**S.element_symbol().type.dict)
    i, j = Symbol(integer=True)
    Eq << apply(All[j:1:n, x:S](Element(Lamda[i:n](Piecewise((x[0], Equal(i, j)), (x[j], Equal(i, 0)), (x[i], True))), S)),
                All[x:S](Equal(Card(x.cup_finiteset()), n)))

    Eq << Discrete.Eq.to.Eq.swap2.general.apply(Eq[0])

    Eq.permutation = Discrete.All_In.to.All_In.swapn.permutation.apply(Eq[-1])

    Eq << Eq.permutation.limits[0][1].this.definition

    Eq << Discrete.Abs.Cup.eq.Factorial.apply(n)

    Eq << Eq[-1].this.lhs.arg.limits_subs(Eq[-1].lhs.arg.variable, Eq[-2].rhs.variable)

    Eq << Eq[-2].apply(Sets.Eq.to.Eq.Card)

    Eq <<= Eq[-2] & Eq[-1]

    F = Function(etype=dtype.integer[n])
    F.eval = lambda e: conditionset(x, Equal(x.cup_finiteset(), e), S)
    e = Symbol(etype=dtype.integer)
    Eq << Subset(F(e), S, plausible=True)

    Eq << Eq[-1].this.lhs.defun()

    Eq << Sets.Subset.All.to.All.apply(Eq[-1], Eq.permutation)

    Eq.all_x = All(Element(Eq[-1].lhs, F(e)), *Eq[-1].limits, plausible=True)

    Eq << Eq.all_x.this.expr.rhs.defun()

    Eq << Algebra.All_And.of.And.All.apply(Eq[-1])

    P = Eq[-1].limits[0][1]
    Eq << Sets.All_Eq_.CupFiniteSet.Range.apply(P)

    Eq << Eq[-1].this.expr.apply(Sets.Eq.to.Eq.permutation, x)

    Eq.equality_e = Eq[-3] & Eq[-1]

    return
    Eq << Sets.All_Eq_.CupFiniteSet.Range.apply(F(e)).reversed
    hat_S = Symbol("\hat{S}", Eq[2].rhs.args[0].arg)
    Eq.hat_S_definition = hat_S.this.definition
    Eq << Equal(S, Cup[e:hat_S](F(e)), plausible=True)
    return
    Eq << Eq[-1].subs(Eq.hat_S_definition)
    Eq << Eq[-1].this.rhs.expr.definition


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-09-14
