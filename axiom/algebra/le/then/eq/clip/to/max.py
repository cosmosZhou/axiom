from util import *


@apply
def apply(le, x):
    a, b = le.of(LessEqual)
    return Equal(clip(x, a, b), Max(Min(x, b), a))


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b = Symbol(real=True)
    Eq << apply(a <= b, x)

    Eq << algebra.le.then.eq.min.apply(Eq[0])

    Eq << Eq[0].reversed

    Eq << Eq[1].this.find(clip).defun()

    Eq << algebra.cond.of.et.infer.split.apply(Eq[-1], cond=a <= x)

    Eq <<= Eq[-2].this.find(Min[~Max]).apply(algebra.max.to.piece.lt), Eq[-1].this.find(Min[~Max]).apply(algebra.max.to.piece.lt)

    Eq <<= Eq[-2].this.lhs.reversed, Eq[-1].this.lhs.reversed

    Eq <<= algebra.infer.of.infer.subs.bool.apply(Eq[-2], invert=True), algebra.infer.of.infer.subs.bool.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(algebra.eq_max.of.ge), Eq[-1].subs(Eq[2])

    Eq <<= Eq[-2].this.rhs.apply(algebra.min_ge.of.et.ge), Eq[-1].this.rhs.apply(algebra.eq_max.of.ge)

    Eq << algebra.infer.of.cond.apply(Eq[-2])

    Eq << Eq[-1].this.lhs.apply(algebra.lt.then.eq.min)

    Eq << Eq[-1].this.lhs.reversed

    Eq << algebra.infer.of.infer.subs.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-03-26
