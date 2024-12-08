from util import *


@apply(simplify=None)
def apply(is_nonpositive):
    x = is_nonpositive.of(Expr <= 0)
    return LessEqual(Ceiling(x), 0)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(real=True)
    Eq << apply(x <= 0)

    Eq << Sets.Any_In_Lopen_Add_1.apply(x)

    Eq << Eq[-1].this.expr.apply(Sets.In_Interval.to.And)

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[0], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.args[:2].apply(Algebra.Gt.Le.to.Lt.trans, ret=0)

    Eq << Eq[-1].this.expr.args[0].apply(Algebra.Lt.to.Le.strengthen)

    Eq << Eq[-1].this.find(Expr <= -1) + 1

    Eq << Eq[-1].this.expr.args[:2].apply(Sets.Gt.Le.to.In.Interval)

    Eq << Eq[-1].this.expr.args[1].apply(Sets.In.to.Eq.Ceiling)

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Le.to.Le.Add)





if __name__ == '__main__':
    run()
# created on 2018-10-30
# updated on 2023-05-13
