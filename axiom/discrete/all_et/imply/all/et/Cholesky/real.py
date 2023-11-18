from util import *


@apply
def apply(all_et):
    (((L, t, i), (((A, S[t], S[i]), (S[L[t, :i]], S[L[i, :i]])), S[L[i, i]])), (S[L[i, i]], S[Interval.open(0, oo)]), (((S[L], S[i], j), S[Reals]), (S[j], S[0], S[i]))), (S[i], S[0], t) = \
    all_et.of(All[Equal[Indexed, (Indexed - MatMul) / Expr] & Element & All[Element[Indexed]]])
    return All[j:t](Element(L[t, j], Reals) & Equal(A[t, j], L[t, :j + 1] @ L[j, :j + 1]))

@prove
def prove(Eq):
    from axiom import algebra, sets, discrete

    n, t = Symbol(integer=True, positive=True)
    A = Symbol(shape=(n, n), real=True)
    L = Symbol(shape=(n, n), super_real=True)
    i, j = Symbol(integer=True)
    Eq << apply(
        All[i:t](Equal(L[t, i],  (A[t, i] - L[t, :i] @ L[i, :i]) / L[i, i]) & Element(L[i, i], Interval.open(0, oo)) & All[j:i](Element(L[i, j], Reals))))

    Eq << algebra.all_et.given.et.all.apply(Eq[1])

    Eq[-1], Eq.Lij_is_real = algebra.all_et.imply.et.all.apply(Eq[0])

    Eq << Eq[-1].this.expr.apply(sets.is_positive.eq.imply.eq.mul, ret=1)

    Eq.Ati_def, Eq.Lii_is_positive = algebra.all_et.imply.et.all.apply(Eq[-1])

    k = Symbol(domain=Range(t), given=False)
    # apply the second mathematical induction
    Eq.hypothesis = All[j:k](Element(L[t, j], Reals), plausible=True)

    Eq.induct = Eq.hypothesis.subs(k, k + 1)

    Eq << algebra.all.given.et.all.split.apply(Eq.induct, cond=Equal(j, k))

    Eq << algebra.all.imply.cond.subs.apply(Eq.Lij_is_real, i, k)

    Eq <<= Eq.hypothesis & Eq[-1]

    Eq << Eq[-1].this.expr.apply(sets.is_real.is_real.imply.is_real)

    Eq << sets.all_is_real.imply.is_real.sum.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(discrete.sum.to.matmul)

    Eq << Element(A[t, k], Reals, plausible=True)

    Eq << sets.is_real.is_real.imply.is_real.sub.apply(Eq[-1], Eq[-2])

    Eq.Lkk_is_positive = algebra.all.imply.cond.subs.apply(Eq.Lii_is_positive, i, k)

    Eq << sets.is_real.is_positive.imply.is_real.apply(Eq[-1], Eq.Lkk_is_positive)

    Eq << algebra.all.imply.cond.subs.apply(Eq.Ati_def, i, k).this.find(MatMul).T

    Eq <<= Eq[-2].subs(Eq[-1].reversed)

    Eq << algebra.et.imply.cond.apply(Eq[-1], -1)

    Eq << Infer(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << algebra.infer.imply.cond.induct.apply(Eq[-1], k, 0)

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq.hypothesis, Eq[-1])

    Eq << Eq.induct.subs(k, t - 1)

    Eq << Eq.Ati_def.this.find(MatMul).apply(discrete.matmul.to.sub.push)

    Eq << Eq[-1].limits_subs(i, j)

    Eq << Eq[-1].this.expr.reversed

    


if __name__ == '__main__':
    run()
# created on 2023-06-29
