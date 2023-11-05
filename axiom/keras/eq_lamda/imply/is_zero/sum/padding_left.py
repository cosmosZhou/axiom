from util import *


@apply
def apply(eq_A):
    ((I, k), limit), A = eq_A.of(Equal[Lamda[Bool[Indexed > 0]]])
    assert I >= 0
    return Equal(Sum[k:ReducedArgMax(A)](I[k]), 0)


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True) # seq_length
    A = Symbol(integer=True, shape=(n,)) # attention_mask = (input_ids > 0).int()
    I = Symbol(integer=True, nonnegative=True, shape=(n,)) # input_ids
    Eq << apply(Equal(A, Lamda[k:n](Bool(I[k] > 0))))

    m = Symbol(Eq[-1].find(ReducedArgMax))
    Eq.m_def = m.this.definition

    Eq << algebra.eq_reducedArgMax.imply.all_gt.apply(Eq.m_def, k)

    Eq << Eq[0][m]

    
    Eq << Eq[-2].subs(Eq[-1])
    Eq << Eq[-1].this.expr.apply(algebra.gt.imply.gt.relax, upper=1)
    Eq << Eq[0][k]
    Eq << Eq[-2].subs(Eq[-1])
    Eq << Eq[-1].this.expr.apply(algebra.lt.imply.le.strengthen)
    Eq << Eq[-1].this.expr.apply(algebra.le_zero.imply.is_zero)
    Eq << Eq[-1].this.expr.apply(algebra.is_zero.imply.cond.invert)
    Eq << Eq[-1].this.expr.apply(algebra.le_zero.imply.is_zero)
    Eq << Eq[-1].subs(Eq.m_def)
    Eq << algebra.all_eq.imply.eq.sum.apply(Eq[-1])
    


if __name__ == '__main__':
    run()
# created on 2023-11-05
