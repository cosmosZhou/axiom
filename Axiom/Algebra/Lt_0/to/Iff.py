from util import *


@apply
def apply(lt_zero, *, cond=None):
    a = lt_zero.of(Expr < 0)
    assert cond.is_Inequality
    lhs, rhs = cond.args
    lhs /= a
    lhs = lhs.ratsimp()
    rhs /= a
    rhs = rhs.ratsimp()
    return Iff(cond, cond.reversed_type(lhs, rhs, evaluate=False), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra

    a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(a < 0, cond= a * x + b < 0)

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[1])

    Eq <<= Algebra.Cond.Imply.of.And.Imply.And.apply(Eq[0], Eq[-2]), Algebra.Cond.Imply.of.And.Imply.And.apply(Eq[0], Eq[-1])

    Eq << Eq[-2].this.lhs.apply(Algebra.Lt_0.Lt.to.Gt.Div)

    Eq << Eq[-1].this.lhs.apply(Algebra.Lt_0.Gt.to.Lt.Mul)

    Eq << Eq[-1].this.lhs.lhs.apply(Algebra.Mul.eq.Add)


if __name__ == '__main__':
    run()
# created on 2023-04-11
