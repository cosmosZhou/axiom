from util import *

@apply
def apply(given):
    from Axiom.Discrete.Alpha.gt.Zero import alpha
    from Axiom.Discrete.H.eq.Add.definition import H
    from Axiom.Discrete.K.eq.Add.definition import K

    (x, j), (S[j], n) = given.of(All[Indexed > 0, Tuple[1, Expr]])
    return Equal(alpha(x[:n]), H(x[:n]) / K(x[:n]))


@prove
def prove(Eq):
    from Axiom import Algebra, Discrete, Logic
    from Axiom.Discrete.Alpha.gt.Zero import alpha
    from Axiom.Discrete.H.eq.Add.definition import H
    from Axiom.Discrete.K.eq.Add.definition import K

    x = Symbol(integer=True, shape=(oo,))
    n = Symbol(integer=True, positive=True)
    j = Symbol(integer=True)
    Eq << apply(All[j:1:n](x[j] > 0))

    Eq << Logic.Cond.given.And.Imp.split.apply(Eq[1], cond=n >= 3)

    Eq.case1, Eq.case2 = Logic.Imp.given.And.Imp.split.apply(Eq[-1], cond=n < 2)

    Eq << Eq.case1.this.lhs.apply(Algebra.Lt.Is.Eq.squeeze)

    Eq << Eq[-1].this.apply(Logic.ImpAndEq.subst)

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(H).defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq.case2.this.apply(Logic.ImpAndEq.subst)

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(H).defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.rhs.rhs.expand()

    n_ = Symbol('n', domain=Range(3, oo))
    Eq << Discrete.Eq.Alpha.HK.of.All_Gt_0.induct.apply(Eq[0].subs(n, n_))

    Eq << Algebra.All.of.Cond.apply(Eq[-1], n_)

    _n = Eq[-1].variable
    Eq << Logic.Imp.of.All.apply(Eq[-1])

    Eq << Eq[-1].subs(_n, n)





if __name__ == '__main__':
    run()

# created on 2020-09-24
# updated on 2023-05-21



from . import induct
from . import offset0
