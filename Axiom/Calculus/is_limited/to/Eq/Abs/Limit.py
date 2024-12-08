from util import *


@apply
def apply(is_limited):
    from Axiom.Calculus.is_limited.to.Any.All.limit_definition import of_limited
    fx, *limits = of_limited(is_limited, real=True)

    return Equal(Limit(abs(fx), *limits), abs(is_limited.lhs))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra, Calculus

    x, x0 = Symbol(real=True)
    g = Function(real=True)
    Eq << apply(Element(Limit[x:x0](g(x)), Reals))

    Eq << Sets.In_Interval.to.Or.apply(Eq[0], 0)

    Eq << Eq[-1].this.args[1].apply(Sets.In_Interval.to.Or, 0, left_open=True, simplify=None)

    Eq << Eq[-1].this.find(Element[FiniteSet]).apply(Sets.In_FiniteSet.to.Eq, simplify=None)

    Eq << Algebra.Cond.of.And.Imply.apply(Eq[1], cond=Eq[-1], simplify=None)

    Eq << Algebra.Imply_Or.of.And.Imply.apply(Eq[-1], None)

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-3])

    Eq << Eq[-1].this.lhs.apply(Calculus.Eq_0.to.Eq_0.Limit.Abs)

    Eq <<= Eq[-2].this.lhs.apply(Sets.is_negative.to.Eq.Abs, ret=0), Eq[-3].this.lhs.apply(Sets.is_positive.to.Eq.Abs, ret=0)

    Eq <<= Algebra.Imply_And.of.Imply.And.subs.apply(Eq[-2]), Algebra.Imply_And.of.Imply.And.subs.apply(Eq[-1])

    Eq <<= Algebra.Imply_And.of.Imply.delete.apply(Eq[-2], 0), Algebra.Imply_And.of.Imply.delete.apply(Eq[-1], 0)

    Eq << Eq[-2].this.lhs.apply(Calculus.is_negative.to.Eq.Limit.Abs)

    Eq << Eq[-1].this.lhs.apply(Calculus.is_positive.to.Eq.Limit.Abs)





if __name__ == '__main__':
    run()
# created on 2023-04-18
# updated on 2023-05-13
