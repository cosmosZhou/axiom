from util import *


@apply
def apply(x, y, z):
    return GreaterEqual(relu(x - y) + Min(y, z), Min(x, z))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x, y, z)

    Eq << Eq[0].this.find(relu).defun()


    Eq << Eq[-1].this.lhs.args[0].apply(Algebra.Max.eq.Piece)

    Eq << Eq[-1].this.lhs.apply(Algebra.Add.eq.Piece)

    Eq << Eq[-1].this.lhs.args[1].expr.apply(Algebra.Add.eq.Min)

    Eq << Eq[-1].this.lhs.args[0].cond.reversed

    Eq << Eq[-1].apply(Algebra.Cond.of.And.Or, cond=x - y <= 0)

    Eq << Algebra.And.of.And.apply(Eq[-1])

    Eq <<= ~Eq[-2], ~Eq[-1]

    Eq <<= Eq[-2].apply(Algebra.Cond.Cond.to.Cond.subs, swap=True, ret=1), Eq[-1].apply(Algebra.Cond.Cond.to.Cond.subs, invert=True, swap=True, ret=1)

    Eq <<= Eq[-2].this.args[1] + y, Eq[-1].this.args[1] + z

    Eq << Eq[-1].this.args[1].apply(Algebra.Gt.to.Ge.Min, x)

    Eq << Eq[-2].this.args[1].apply(Algebra.Le.to.Le.Min, z)





if __name__ == '__main__':
    run()
# created on 2020-12-27
# updated on 2022-01-08