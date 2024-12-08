from util import *


@apply
def apply(given):
    abs_x, a = given.of(Less)
    x = abs_x.of(Expr ** 2)
    assert x.is_real
    return Less(x, sqrt(a)), Less(-sqrt(a), x)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x, a = Symbol(real=True)
    Eq << apply(x ** 2 < a ** 2)

    Eq << Algebra.Lt.to.Lt_0.apply(Eq[0])

    Eq << Eq[-1].this.lhs.apply(Algebra.Sub.Square.eq.Mul)

    Eq << Algebra.Lt_0.to.Or.split.Mul.apply(Eq[-1])

    Eq << Eq[-1].this.args[0].args[0].apply(Algebra.Lt.transport, lhs=0)

    Eq << Eq[-1].this.args[0].args[1].apply(Algebra.Gt.transport, lhs=1)

    Eq << Eq[-1].this.args[0].apply(Sets.Lt.Gt.to.In.Interval)

    Eq << Eq[-1].this.args[1].args[0].apply(Algebra.Lt.transport, lhs=1)

    Eq << Eq[-1].this.args[1].args[1].apply(Algebra.Gt.transport, lhs=0)

    Eq << Eq[-1].this.args[1].apply(Sets.Lt.Gt.to.In.Interval)

    Eq << Eq[-1].this.rhs.apply(Sets.Union.eq.Interval.Abs)

    Eq << Sets.In_Interval.to.And.apply(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2023-06-18
