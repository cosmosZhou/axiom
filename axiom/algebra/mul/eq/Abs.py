from util import *


@apply
def apply(self, evaluate=False):
    args = []

    for arg in self.of(Mul):
        if arg.is_Abs:
            args.append(arg.of(Abs))
            continue
        elif arg.is_Pow:
            if arg.base.is_Abs and arg.exp.is_integer:
                args.append(Pow(arg.base.of(Abs), arg.exp))
                continue

        assert arg >= 0
        args.append(arg)

    return Equal(self, Abs(Mul(*args), evaluate=evaluate))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True)
    Eq << apply(abs(x) * abs(y))

    Eq << Eq[-1].this.lhs.find(Abs).apply(Algebra.Abs.eq.Piece)

    Eq << Eq[-1].this.lhs.find(Abs).apply(Algebra.Abs.eq.Piece)

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul.Piece.eq.Piece)

    Eq << Eq[-1].this.lhs.apply(Algebra.Piece.unnest)

    Eq << Eq[-1].this.lhs.apply(Algebra.Piece.swap, -2)

    Eq << Eq[-1].this.lhs.args[0].cond.apply(Algebra.And.equ.Or)

    Eq << Eq[-1].this.lhs.args[0].expr.apply(Algebra.Mul.eq.Piece.And.Ne_0)

    Eq << Eq[-1].this.lhs.apply(Algebra.Piece.unnest, index=0)

    Eq << Eq[-1].this.lhs.args[0].cond.apply(Algebra.And.equ.Or)

    Eq << Eq[-1].this.lhs.apply(Algebra.Piece.And.invert, 0)

    Eq.equal = Eq[-1].this.lhs.args[1].cond.apply(Algebra.And.equ.Or)

    Eq.suffice = Imply(Eq.equal.lhs.args[1].cond, Equal(x * y, 0), plausible=True)

    Eq << Algebra.Imply_Or.of.And.Imply.apply(Eq.suffice)

    Eq <<= Eq[-1].this.lhs.apply(Algebra.And.to.Cond, index=0), Eq[-2].this.lhs.apply(Algebra.And.to.Cond, index=0)

    Eq << Eq[-2].this.lhs * x

    Eq << Eq[-1].this.lhs * y

    Eq << -Eq.suffice.this.rhs

    Eq << Eq[-1].apply(Algebra.Imply.to.Iff)

    Eq << Algebra.Iff.to.Eq.subs.apply(Eq[-1], Eq.equal.lhs)

    Eq << Eq[-1].this.rhs.apply(Algebra.Piece.subs, index=1, reverse=True)

    Eq << Eq.equal.this.lhs.subs(Eq[-1])

    Eq.equal = Eq[-1].this.rhs.apply(Algebra.Abs.eq.Piece.Gt_0)

    Eq.equivalent = Iff(Eq.equal.lhs.args[0].cond, Eq.equal.rhs.args[0].cond, plausible=True)

    Eq.suffice, Eq.necessary = Algebra.Iff.of.And.apply(Eq.equivalent)

    Eq << Algebra.Imply_Or.of.And.Imply.apply(Eq.suffice)

    Eq << Eq[-2].this.lhs.apply(Algebra.Lt_0.Lt_0.to.Gt_0)

    Eq << Eq[-1].this.lhs.apply(Algebra.Gt_0.Gt_0.to.Gt_0)

    Eq << Eq.necessary.this.rhs.apply(Algebra.Gt_0.to.Or)

    Eq << Algebra.Iff.to.Eq.subs.apply(Eq.equivalent, Eq.equal.lhs)


if __name__ == '__main__':
    run()

# created on 2018-02-11
# updated on 2023-05-19
