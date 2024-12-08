from util import *


@apply
def apply(given):
    from Axiom.Discrete.Alpha.gt.Zero import alpha
    from Axiom.Discrete.H.eq.Add.definition import H
    from Axiom.Discrete.K.eq.Add.definition import K

    (x, _j), (j, n) = given.of(All[Indexed > 0, Tuple[0, Expr]])
    offset = _j - j
    if offset != 0:
        assert not offset._has(j)
        x = x[offset:]
    return Equal(alpha(x[:n]), H(x[:n]) / K(x[:n]))


@prove
def prove(Eq):
    from Axiom import Discrete, Algebra, Sets
    from Axiom.Discrete.Alpha.gt.Zero import alpha

    x = Symbol(real=True, shape=(oo,))
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    Eq << apply(All[i:n](x[i] > 0))

    x_ = Symbol('x', real=True, positive=True, shape=(oo,))
    Eq << Discrete.Alpha.eq.Mul.HK.st.Gt_0.apply(alpha(x_[:n]))

    Eq << Eq[-1].subs(x_[:n], x[:n])

    Eq << Algebra.Or.to.Imply.apply(Eq[-1], 1)

    Eq << Eq[-1].this.lhs.apply(Sets.In_CartesianSpace.of.All.In)

    Eq << Eq[-1].this.lhs.expr.simplify()
    Eq << Algebra.Cond.Imply.to.Cond.trans.apply(Eq[0], Eq[-1])





if __name__ == '__main__':
    run()

# created on 2020-09-20
# updated on 2023-08-20
