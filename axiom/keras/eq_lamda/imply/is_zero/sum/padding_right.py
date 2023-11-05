from util import *


@apply
def apply(eq_A):
    ((I, k), limit), A = eq_A.of(Equal[Lamda[Bool[Indexed > 0]]])
    assert I >= 0
    n, = A.shape
    return Equal(Sum[k:ReducedArgMax(A * Lamda[k:n](k)) + 1:n](I[k]), 0)


@prove
def prove(Eq):
    from axiom import algebra, sets

    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True) # seq_length
    A = Symbol(integer=True, shape=(n,)) # attention_mask = (input_ids > 0).int()
    I = Symbol(integer=True, nonnegative=True, shape=(n,)) # input_ids
    Eq << apply(Equal(A, Lamda[k:n](Bool(I[k] > 0))))

    m = Symbol(Eq[-1].find(ReducedArgMax))
    Eq.m_def = m.this.definition

    Eq << algebra.eq_reducedArgMax.imply.all_ge.apply(Eq.m_def, k, simplify=None)

    Eq << Eq[0][m] * m

    Eq << Eq[-2].subs(Eq[-1])

    Eq << algebra.all.imply.all.limits.restrict.apply(Eq[-1], Range(m + 1, n))

    Eq << LessEqual(Eq[-1].find(Bool), 1, plausible=True)

    Eq << Eq[-1] * m

    Eq << algebra.cond.all.imply.all.et.apply(Eq[-1], Eq[-3], simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.le.ge.imply.ge.transit)

    Eq << Eq[0][k] * k
    Eq << Eq[-2].subs(Eq[-1])
    Eq << algebra.all.imply.all_et.apply(Eq[-1])
    Eq << Eq[-1].this.find(Element).apply(sets.el_range.imply.ge)
    Eq << Eq[-1].this.find(GreaterEqual[2]).apply(algebra.ge.imply.gt_zero, ret=True, simplify=None)
    Eq << Eq[-1].this.find(Greater).apply(algebra.gt_zero.imply.gt_zero.div)
    Eq << Eq[-1].this.expr.args[:2].apply(algebra.gt_zero.ge.imply.ge.mul, ret=0)
    Eq << Eq[-1].this.find(GreaterEqual).apply(algebra.ge.imply.gt.relax)
    Eq << Eq[-1].this.expr.args[:2].apply(algebra.gt_zero.gt.imply.gt.mul)
    Eq << Eq[-1].this.expr.apply(algebra.lt.ge.imply.lt.transit)
    Eq << Eq[-1].this.expr.apply(algebra.lt.imply.le.strengthen)
    Eq << Eq[-1].this.expr.apply(algebra.le_zero.imply.is_zero)
    Eq << Eq[-1].this.expr.apply(algebra.is_zero.imply.cond.invert)
    Eq << Eq[-1].this.expr.apply(algebra.le_zero.imply.is_zero)
    Eq << algebra.all_eq.imply.eq.sum.apply(Eq[-1])
    Eq << Eq[-1].subs(Eq.m_def)
    


if __name__ == '__main__':
    run()
# created on 2023-11-05
