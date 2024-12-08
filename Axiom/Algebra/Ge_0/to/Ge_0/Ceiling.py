from util import *


@apply(simplify=None)
def apply(is_nonnegative):
    x = is_nonnegative.of(Expr >= 0)
    return GreaterEqual(Ceiling(x), 0)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(real=True)
    Eq << apply(x >= 0)

    Eq << Sets.Any_In_Lopen_Add_1.apply(x)

    Eq << Eq[-1].this.expr.apply(Sets.In_Interval.to.And)

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[0], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.args[1:].apply(Algebra.Le.Ge.to.Ge.trans, ret=0)

    Eq << Eq[-1].this.expr.args[:2].apply(Sets.Gt.Le.to.In.Interval)

    Eq << Eq[-1].this.expr.args[1].apply(Sets.In.to.Eq.Ceiling)

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Ge.to.Ge.Add)




if __name__ == '__main__':
    run()
# created on 2019-03-11
# updated on 2023-05-14
