from util import *


def reverse(x):
    n = x.shape[0]
    i = x.generate_var(integer=True, free_symbols='i')
    return Lamda[i:n](x[n - 1 - i])


@apply
def apply(x):
    from Axiom.Discrete.Alpha.gt.Zero import alpha
    from Axiom.Discrete.H.eq.Add.definition import H

    n = x.shape[0]
    assert x.is_positive
    assert n >= 2
    return Equal(alpha(reverse(x)), H(x[:n]) / H(x[:n - 1]))


@prove
def prove(Eq):
    from Axiom import Discrete, Algebra
    from Axiom.Discrete.Alpha.gt.Zero import alpha
    from Axiom.Discrete.H.eq.Add.definition import H

    x = Symbol(real=True, positive=True, shape=(oo,))
#     x = Symbol(real=True, shape=(oo,))
    n = Symbol(domain=Range(2, oo), given=False)

    Eq << apply(x[:n])

    Eq.initial = Eq[0].subs(n, 2)

    Eq << Eq.initial.this.find(Lamda).apply(Algebra.Lamda.eq.Matrix)

    Eq << Eq[-1].this.lhs.apply(Discrete.Alpha.Matrix)

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(H).defun()

    Eq << Eq[-1].this.find(H).defun()

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.eq.Add)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.defun()

    Eq << Eq[-1].this.find(H).defun()

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.eq.Add)

    Eq << Discrete.Alpha.ne.Zero.apply(reverse(x[:n]))

    Eq << Algebra.Ne_0.Eq.to.Eq.Inv.apply(Eq[-1], Eq[0])

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Algebra.Eq.Imply.to.Eq.induct.apply(Eq.initial, Eq[-1], n=n, start=2)


if __name__ == '__main__':
    run()

# created on 2020-09-27
