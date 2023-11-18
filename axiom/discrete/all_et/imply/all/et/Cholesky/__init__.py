from util import *


@apply
def apply(all_et):
    (((L, t, i), (((A, S[t], S[i]), (S[L[t, :i]], S[~L[i, :i]])), S[L[i, i]])), (S[L[i, i]], S[Interval.open(0, oo)]), (((S[L], S[i], j), S[S.Complexes]), (S[j], S[0], S[i]))), (S[i], S[0], t) = \
    all_et.of(All[Equal[Indexed, (Indexed - MatMul) / Expr] & Element & All[Element[Indexed]]])
    return All[j:t](Element(L[t, j], S.Complexes) & Equal(A[t, j], L[t, :j + 1] @ ~L[j, :j + 1]))

@prove
def prove(Eq):
    from axiom import algebra, sets, discrete

    n, t = Symbol(integer=True, positive=True)
    A = Symbol(shape=(n, n), complex=True)
    L = Symbol(shape=(n, n), super_complex=True)
    i, j = Symbol(integer=True)
    Eq << apply(
        All[i:t](Equal(L[t, i],  (A[t, i] - L[t, :i] @ ~L[i, :i]) / L[i, i]) & Element(L[i, i], Interval.open(0, oo)) & All[j:i](Element(L[i, j], S.Complexes))))

    Eq << algebra.all_et.given.et.all.apply(Eq[1])

    Eq[-1], Eq.Lij_is_complex = algebra.all_et.imply.et.all.apply(Eq[0])

    Eq << Eq[-1].this.expr.apply(sets.is_positive.eq.imply.eq.mul, ret=1)

    Eq.Ati_def, Eq.Lii_is_positive = algebra.all_et.imply.et.all.apply(Eq[-1])

    k = Symbol(domain=Range(t), given=False)
    # apply the second mathematical induction
    Eq.hypothesis = All[j:k](Element(L[t, j], S.Complexes), plausible=True)

    Eq.induct = Eq.hypothesis.subs(k, k + 1)

    Eq << algebra.all.given.et.all.split.apply(Eq.induct, cond=Equal(j, k))

    Eq.Lij_conj_is_complex = Eq.Lij_is_complex.this.expr.apply(sets.is_complex.imply.is_complex.conj)

    Eq << algebra.all.imply.cond.subs.apply(Eq.Lij_conj_is_complex, i, k)

    Eq <<= Eq.hypothesis & Eq[-1]

    Eq << Eq[-1].this.expr.apply(sets.is_complex.is_complex.imply.is_complex)

    Eq << sets.all_is_complex.imply.is_complex.sum.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(discrete.sum.to.matmul)

    Eq << Element(A[t, k], S.Complexes, plausible=True)

    Eq << sets.is_complex.is_complex.imply.is_complex.sub.apply(Eq[-1], Eq[-2])

    Eq.Lkk_is_positive = algebra.all.imply.cond.subs.apply(Eq.Lii_is_positive, i, k)

    Eq << sets.is_complex.is_positive.imply.is_complex.apply(Eq[-1], Eq.Lkk_is_positive)

    Eq << algebra.all.imply.cond.subs.apply(Eq.Ati_def, i, k)

    Eq <<= Eq[-2].subs(Eq[-1].reversed)

    Eq << algebra.et.imply.cond.apply(Eq[-1], -1)

    Eq << Infer(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << algebra.infer.imply.cond.induct.apply(Eq[-1], k, 0)

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq.hypothesis, Eq[-1])

    Eq << Eq.induct.subs(k, t - 1)

    Eq << Eq.Ati_def.this.find(MatMul).apply(discrete.matmul.to.sum)

    Eq << algebra.all.all.imply.all.et.apply(Eq.Lij_conj_is_complex, Eq[3])

    Eq << Eq[-1].this.apply(algebra.all.limits.separate, simplify=None)

    Eq << Eq[-1].this().find(Min).simplify()

    Eq << Eq[-1].this.expr.apply(sets.is_complex.is_complex.imply.is_complex)

    Eq << Eq[-1].this.apply(algebra.all.limits.separate, simplify=None)

    Eq << Eq[-1].this.expr.apply(sets.all_is_complex.imply.is_complex.sum)

    Eq << Eq[-1].this.find(Sum).apply(discrete.sum.to.matmul)

    Eq << algebra.all.all.imply.all.et.apply(Eq.Ati_def, Eq[-1])

    Eq << Eq[-1].this.expr.apply(sets.is_complex.eq.imply.eq.add)

    Eq << Eq[-1].this.expr.reversed

    Eq << Eq.Lii_is_positive.this.expr.apply(sets.is_real.imply.eq.conj, reverse=True)

    Eq << algebra.all.all.imply.all.et.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.expr.apply(algebra.eq.eq.imply.eq.subs, swap=True)

    Eq << Eq[-1].this.find(MatMul).apply(discrete.matmul.to.sub.push)

    Eq << Eq[-1].limits_subs(i, j)

    


if __name__ == '__main__':
    run()
# created on 2023-06-05
# updated on 2023-06-27
from . import real
