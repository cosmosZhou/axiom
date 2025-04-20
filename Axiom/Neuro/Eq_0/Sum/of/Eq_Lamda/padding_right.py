from util import *


@apply
def apply(eq_A):
    ((I, k), limit), A = eq_A.of(Equal[Lamda[Bool[Indexed > 0]]])
    assert I >= 0
    n, = A.shape
    return Equal(Sum[k:ReducedArgMax(A * Lamda[k:n](k)) + 1:n](I[k]), 0)


@prove
def prove(Eq):
    from Axiom import Algebra, Set

    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True) # seq_length
    A = Symbol(integer=True, shape=(n,)) # attention_mask = (input_ids > 0).int()
    I = Symbol(integer=True, nonnegative=True, shape=(n,)) # input_ids
    Eq << apply(Equal(A, Lamda[k:n](Bool(I[k] > 0))))

    m = Symbol(Eq[-1].find(ReducedArgMax))
    Eq.m_def = m.this.definition

    Eq << Algebra.All.Ge.of.Eq_ReducedArgMax.apply(Eq.m_def, k, simplify=None)

    Eq << Eq[0][m] * m

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Algebra.All.of.All.limits.restrict.apply(Eq[-1], Range(m + 1, n))

    Eq << LessEqual(Eq[-1].find(Bool), 1, plausible=True)

    Eq << Eq[-1] * m

    Eq << Algebra.All.And.of.Cond.All.apply(Eq[-1], Eq[-3], simplify=None)

    Eq << Eq[-1].this.expr.apply(Algebra.Ge.of.Le.Ge)

    Eq << Eq[0][k] * k
    Eq << Eq[-2].subs(Eq[-1])
    Eq << Algebra.All.And.of.All.apply(Eq[-1])
    Eq << Eq[-1].this.find(Element).apply(Set.Ge.of.Mem_Range)
    Eq << Eq[-1].this.find(GreaterEqual[2]).apply(Algebra.Gt_0.of.Ge, ret=True, simplify=None)
    Eq << Eq[-1].this.find(Greater).apply(Algebra.Gt_0.Div.of.Gt_0)
    Eq << Eq[-1].this.expr.args[:2].apply(Algebra.GeMul.of.Gt_0.Ge, ret=0)
    Eq << Eq[-1].this.find(GreaterEqual).apply(Algebra.Gt.of.Ge.relax)
    Eq << Eq[-1].this.expr.args[:2].apply(Algebra.GtMul.of.Gt_0.Gt)
    Eq << Eq[-1].this.expr.apply(Algebra.Lt.of.Lt.Ge)
    Eq << Eq[-1].this.expr.apply(Algebra.Le.of.Lt.strengthen)
    Eq << Eq[-1].this.expr.apply(Algebra.Eq_0.of.Le_0)
    Eq << Eq[-1].this.expr.apply(Algebra.Cond.of.Eq_0.invert)
    Eq << Eq[-1].this.expr.apply(Algebra.Eq_0.of.Le_0)
    Eq << Algebra.EqSum.of.All_Eq.apply(Eq[-1])
    Eq << Eq[-1].subs(Eq.m_def)



if __name__ == '__main__':
    run()
# created on 2023-11-05
