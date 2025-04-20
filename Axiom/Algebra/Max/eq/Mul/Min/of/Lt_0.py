from util import *


@apply
def apply(is_negative, self, div=False):
    factor = is_negative.of(Expr < 0)
    args = self.of(Max)

    if div:
        args = [arg * factor for arg in args]
        rhs = Min(*args) / factor
    else:
        args = [arg / factor for arg in args]
        rhs = Min(*args) * factor

    return Equal(self, rhs)


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    x, y = Symbol(real=True)
    r = Symbol(real=True)
    Eq << apply(r < 0, Max(r * x, r * y))

    Eq << Eq[-1].this.lhs.apply(Algebra.Max.eq.Ite)

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Min.eq.Ite)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ite.eq.Mul)

    Eq.eq = Algebra.Eq.given.Eq.Div.apply(Eq[-1], r)

    Eq.equivalent = Iff(Eq[-1].find(GreaterEqual), Eq[-1].rhs.find(LessEqual), plausible=True)

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq.equivalent)

    Eq <<= Logic.Cond.Imp.given.And.Imp.And.apply(Eq[0], Eq[-2]), Algebra.Given.given.Given_And.apply(Eq[-1], cond=Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Algebra.LeDiv.of.Lt_0.Ge), Eq[-1].this.rhs.apply(Algebra.GeMul.of.Lt_0.Le)

    Eq << Algebra.Cond.given.Cond.subs.Cond.apply(Eq.eq, old=Eq.equivalent.lhs, new=Eq.equivalent.rhs)





if __name__ == '__main__':
    run()
# created on 2020-01-19
# updated on 2021-10-02
