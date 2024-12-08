from util import *

@apply
def apply(self):
    from Axiom.Discrete.Alpha.gt.Zero import alpha
    from Axiom.Discrete.H.eq.Add.definition import H
    from Axiom.Discrete.K.eq.Add.definition import K
    x = self.of(alpha)
    n = x.shape[0]
    assert n >= 3
    return Equal(self, H(x[:n]) / K(x[:n]))


@prove
def prove(Eq):
    from Axiom import Discrete, Algebra
    from Axiom.Discrete.Alpha.gt.Zero import alpha
    from Axiom.Discrete.H.eq.Add.definition import H
    from Axiom.Discrete.K.eq.Add.definition import K

    x = Symbol(real=True, positive=True, shape=(oo,))
    n = Symbol(domain=Range(2, oo), given=False)
    Eq << apply(alpha(x[:n + 1]))

    Eq.initial = Eq[-1].subs(n, 2)

    Eq <<= alpha(x[:3]).this.defun(), H(x[:3]).this.defun(), K(x[:3]).this.defun()

    Eq <<= Eq[-3].this.rhs.subs(alpha(x[1:3]).this.defun()), Eq[-2].this.rhs.subs(H(x[:2]).this.defun()), Eq[-1].this.rhs.subs(K(x[:2]).this.defun())

    Eq <<= Eq[-3].this.rhs.subs(alpha(x[2]).this.defun()), Eq[-2].this.rhs.subs(H(x[0]).this.defun()), Eq[-1].this.rhs.subs(K(x[0]).this.defun())

    Eq << Eq.initial.subs(Eq[-3], Eq[-2], Eq[-1])

    Eq << Discrete.K.ne.Zero.apply(x[:3])

    Eq << Algebra.And.of.And.apply(Eq[-2])


    Eq << Eq[-1].this.lhs.args[1].apply(Algebra.Pow.eq.Mul.st.Inv, x[2])

    Eq << Eq[-1] * (x[1] * x[2] + 1)

    Eq << Eq[-1].this.lhs.ratsimp()

    Eq << Eq[-1].this.rhs.expand()

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(Discrete.Alpha.recurrence)

    Eq << Eq[-1].this.rhs.args[0].defun()

    Eq << Eq[-1].this.rhs.args[1].base.defun()

    Eq << H(x[:n + 1]).this.defun()

    Eq << K(x[:n + 1]).this.defun()

    Eq << Eq[-3].this.rhs.subs(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.rhs.args[0].expand()

    Eq << Eq[-1].this.rhs.args[0].base.expand()

    Eq << Algebra.Cond.to.Cond.subs.apply(Eq[0], x[:n + 1], BlockMatrix(x[:n], x[n] + 1 / x[n + 1]))

    Eq << Eq[-1].this.lhs.apply(Discrete.Alpha.Block)

    Eq << Eq[-1].this.rhs.args[0].defun()

    Eq << Eq[-1].this.rhs.args[1].base.defun()

    Eq << Eq[-1].this.rhs.apply(Algebra.Div.cancel, x[n + 1])

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Algebra.Cond.Imply.to.Cond.induct.apply(Eq.initial, Eq[-1], n=n, start=2)


if __name__ == '__main__':
    run()

# created on 2020-09-19
# updated on 2023-04-05
