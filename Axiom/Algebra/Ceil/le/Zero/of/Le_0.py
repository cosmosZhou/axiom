from util import *


@apply(simplify=None)
def apply(is_nonpositive):
    x = is_nonpositive.of(Expr <= 0)
    return LessEqual(Ceil(x), 0)


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    x = Symbol(real=True)
    Eq << apply(x <= 0)

    Eq << Set.Any_Mem_Ioc_Add_1.apply(x)

    Eq << Eq[-1].this.expr.apply(Set.And.of.Mem_Icc)

    Eq << Algebra.Any.And.of.Cond.Any.apply(Eq[0], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.args[:2].apply(Algebra.Lt.of.Gt.Le, ret=0)

    Eq << Eq[-1].this.expr.args[0].apply(Algebra.Le.of.Lt.strengthen)

    Eq << Eq[-1].this.find(Expr <= -1) + 1

    Eq << Eq[-1].this.expr.args[:2].apply(Set.Mem.Icc.of.Gt.Le)

    Eq << Eq[-1].this.expr.args[1].apply(Set.EqCeil.of.Mem_Ioc)

    Eq << Eq[-1].this.expr.apply(Algebra.LeAdd.of.Eq.Le)





if __name__ == '__main__':
    run()
# created on 2018-10-30
# updated on 2023-05-13
