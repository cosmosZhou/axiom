from util import *


@apply
def apply(x):
    from Axiom.Discrete.Alpha.gt.Zero import alpha
    from Axiom.Discrete.K.eq.Add.definition import K

    n = x.shape[0]
    n -= 1
    assert n >= 2
    return Equal(alpha(x[:n + 1]), alpha(x[:n - 1]) + (-1) ** n * x[n] / (K(x[:n + 1]) * K(x[:n - 1])))


@prove
def prove(Eq):
    from Axiom import Discrete
    from Axiom.Discrete.Alpha.gt.Zero import alpha

    x = Symbol(real=True, positive=True, shape=(oo,))
    n = Symbol(domain=Range(2, oo))

    Eq << apply(x[:n + 1])

    Eq << Eq[0].this.lhs.apply(Discrete.Alpha.eq.Mul.HK.st.Gt_0)

    Eq << Eq[-1].this.find(alpha).apply(Discrete.Alpha.eq.Mul.HK.st.Gt_0)

    Eq << Eq[-1] - Eq[-1].rhs.args[0]

    Eq << Eq[-1].this.lhs.together()

    Eq << Discrete.Add.eq.Mul.HK.step2.apply(x[:n + 1])


if __name__ == '__main__':
    run()

# created on 2020-09-25
