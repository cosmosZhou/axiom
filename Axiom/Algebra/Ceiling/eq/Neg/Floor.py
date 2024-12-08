from util import *


@apply
def apply(ceil):
    x = ceil.of(Ceiling)

    return Equal(ceil, -floor(-x))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x = Symbol(real=True)
    Eq << apply(ceiling(x))

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=Element(x, Integers))

    Eq << Eq[-2].this.lhs.apply(Sets.In.to.Any.Eq)

    Eq << Eq[-1].this.lhs.expr.apply(Algebra.Eq.to.Eq.Ceiling, ret=0)

    Eq << -Eq[-1].this.lhs.expr.args[0]

    Eq << Eq[-1].this.lhs.expr.args[0].apply(Algebra.Eq.to.Eq.Floor)

    Eq << Eq[-1].this.lhs.expr.apply(Algebra.Eq.Eq.to.Eq.Add)

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.of.Eq_0)

    Eq << Eq[2].this.lhs.apply(Sets.is_noninteger.to.Eq.Ceiling, ret=0)

    Eq << Eq[-1].this.find(NotElement).apply(Sets.NotIn.to.Eq.Floor.Frac)

    Eq << Eq[-1].this.find(frac).apply(Algebra.Frac.eq.Add)

    Eq << Eq[-1].this.lhs.apply(Algebra.Eq.Eq.to.Eq.Add)




if __name__ == '__main__':
    run()
# created on 2018-05-21
# updated on 2023-05-14
