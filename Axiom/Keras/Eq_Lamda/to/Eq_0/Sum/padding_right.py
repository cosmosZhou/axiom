from util import *


@apply
def apply(eq_A):
    ((I, k), limit), A = eq_A.of(Equal[Lamda[Bool[Indexed > 0]]])
    assert I >= 0
    n, = A.shape
    return Equal(Sum[k:ReducedArgMax(A * Lamda[k:n](k)) + 1:n](I[k]), 0)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True) # seq_length
    A = Symbol(integer=True, shape=(n,)) # attention_mask = (input_ids > 0).int()
    I = Symbol(integer=True, nonnegative=True, shape=(n,)) # input_ids
    Eq << apply(Equal(A, Lamda[k:n](Bool(I[k] > 0))))

    m = Symbol(Eq[-1].find(ReducedArgMax))
    Eq.m_def = m.this.definition

    Eq << Algebra.Eq_ReducedArgMax.to.All.Ge.apply(Eq.m_def, k, simplify=None)

    Eq << Eq[0][m] * m

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Algebra.All.to.All.limits.restrict.apply(Eq[-1], Range(m + 1, n))

    Eq << LessEqual(Eq[-1].find(Bool), 1, plausible=True)

    Eq << Eq[-1] * m

    Eq << Algebra.Cond.All.to.All.And.apply(Eq[-1], Eq[-3], simplify=None)

    Eq << Eq[-1].this.expr.apply(Algebra.Le.Ge.to.Ge.trans)

    Eq << Eq[0][k] * k
    Eq << Eq[-2].subs(Eq[-1])
    Eq << Algebra.All.to.All.And.apply(Eq[-1])
    Eq << Eq[-1].this.find(Element).apply(Sets.In_Range.to.Ge)
    Eq << Eq[-1].this.find(GreaterEqual[2]).apply(Algebra.Ge.to.Gt_0, ret=True, simplify=None)
    Eq << Eq[-1].this.find(Greater).apply(Algebra.Gt_0.to.Gt_0.Div)
    Eq << Eq[-1].this.expr.args[:2].apply(Algebra.Gt_0.Ge.to.Ge.Mul, ret=0)
    Eq << Eq[-1].this.find(GreaterEqual).apply(Algebra.Ge.to.Gt.relax)
    Eq << Eq[-1].this.expr.args[:2].apply(Algebra.Gt_0.Gt.to.Gt.Mul)
    Eq << Eq[-1].this.expr.apply(Algebra.Lt.Ge.to.Lt.trans)
    Eq << Eq[-1].this.expr.apply(Algebra.Lt.to.Le.strengthen)
    Eq << Eq[-1].this.expr.apply(Algebra.Le_0.to.Eq_0)
    Eq << Eq[-1].this.expr.apply(Algebra.Eq_0.to.Cond.invert)
    Eq << Eq[-1].this.expr.apply(Algebra.Le_0.to.Eq_0)
    Eq << Algebra.All_Eq.to.Eq.Sum.apply(Eq[-1])
    Eq << Eq[-1].subs(Eq.m_def)



if __name__ == '__main__':
    run()
# created on 2023-11-05
