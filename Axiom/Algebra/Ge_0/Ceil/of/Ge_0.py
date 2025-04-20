from util import *


@apply(simplify=None)
def apply(is_nonnegative):
    x = is_nonnegative.of(Expr >= 0)
    return GreaterEqual(Ceil(x), 0)


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    x = Symbol(real=True)
    Eq << apply(x >= 0)

    Eq << Set.Any_Mem_Ioc_Add_1.apply(x)

    Eq << Eq[-1].this.expr.apply(Set.And.of.Mem_Icc)

    Eq << Algebra.Any.And.of.Cond.Any.apply(Eq[0], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.args[1:].apply(Algebra.Ge.of.Le.Ge, ret=0)

    Eq << Eq[-1].this.expr.args[:2].apply(Set.Mem.Icc.of.Gt.Le)

    Eq << Eq[-1].this.expr.args[1].apply(Set.EqCeil.of.Mem_Ioc)

    Eq << Eq[-1].this.expr.apply(Algebra.GeAdd.of.Eq.Ge)




if __name__ == '__main__':
    run()
# created on 2019-03-11
# updated on 2023-05-14
