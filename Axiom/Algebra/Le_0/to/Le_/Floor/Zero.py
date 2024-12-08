from util import *


@apply(simplify=None)
def apply(is_nonpositive):
    x = is_nonpositive.of(Expr <= 0)
    return LessEqual(Floor(x), 0)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(real=True)
    Eq << apply(x <= 0)

    Eq << Sets.Any_In_Ropen.apply(x)

    Eq << Eq[-1].this.expr.apply(Sets.In_Interval.to.And)

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[0], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.args[1:].apply(Algebra.Le.Ge.to.Ge.trans, ret=1)

    Eq << Eq[-1].this.expr.args[::2].apply(Sets.Lt.Ge.to.In.Interval)

    Eq << Eq[-1].this.expr.args[1].apply(Sets.In.to.Eq.Floor)

    Eq << Eq[-1].this.expr.apply(Algebra.Ge.Eq.to.Ge.trans)

    Eq << Eq[-1].reversed




if __name__ == '__main__':
    run()
# created on 2019-12-06
# updated on 2023-05-18
