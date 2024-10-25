from util import *


@apply
def apply(is_positive, self):
    factor = is_positive.of(Expr > 0)
    args = self.of(Max)

    args = [arg * factor for arg in args]
    return Equal(Max(*args), self * factor)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    r = Symbol(real=True)
    Eq << apply(r > 0, Max(x, y))

    Eq << Eq[-1].this.lhs.apply(algebra.max.to.piece)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.max.to.piece)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.to.mul)

    Eq.eq = algebra.eq.of.eq.div.apply(Eq[-1], r)

    Eq.equivalent = Equivalent(Eq[-1].find(GreaterEqual), Eq[-1].rhs.find(GreaterEqual), plausible=True)

    Eq << algebra.iff.of.et.apply(Eq.equivalent)

    Eq <<= algebra.cond.infer.of.et.infer.et.apply(Eq[0], Eq[-2]), algebra.assuming.of.assuming_et.apply(Eq[-1], cond=Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(algebra.gt_zero.ge.then.ge.div), Eq[-1].this.rhs.apply(algebra.gt_zero.ge.then.ge.mul)

    Eq << algebra.cond.of.cond.subs.cond.apply(Eq.eq, old=Eq.equivalent.lhs, new=Eq.equivalent.rhs)


if __name__ == '__main__':
    run()
# created on 2019-08-16
