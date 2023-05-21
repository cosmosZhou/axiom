from util import *


@apply
def apply(self):
    (A, r), ((S[r], epsilon_less, epsilon_more), S[A]) = self.of(Min[Mul, Mul[clip]])
    ε = (epsilon_more - epsilon_less) / 2
    assert epsilon_more + epsilon_less == 2
    assert 0 < ε < 1
    return Equal(self, A * Piecewise((Piecewise((1 + ε, r > 1 + ε), (r, True)), A >= 0), (Piecewise((1 - ε, r <= 1 - ε), (r, True)), True)))


@prove
def prove(Eq):
    from axiom import algebra

    ε = Symbol(domain=Interval(0, 1, left_open=True, right_open=True))
    #0 < ε < 1
    r_t = Symbol(real=True, positive=True)
    A_t = Symbol(real=True)
    Eq << apply(Min(r_t * A_t, clip(r_t, 1 - ε, 1 + ε) * A_t))

    Eq << algebra.cond.given.et.infer.split.apply(Eq[0], cond=Eq[-1].find(GreaterEqual))

    Eq <<= algebra.infer.given.infer.subs.bool.apply(Eq[-2]), algebra.infer.given.infer.subs.bool.apply(Eq[-1], invert=True)

    Eq << algebra.infer.given.et.infer.split.apply(Eq[-2], cond=A_t > 0)

    Eq << algebra.infer.given.infer.subs.apply(Eq[-1])

    Eq <<= algebra.infer.given.infer.et.apply(Eq[-3]), algebra.infer.given.infer.et.apply(Eq[-2])

    Eq <<= Eq[-2].this.rhs.apply(algebra.lt_zero.eq.given.et.div), Eq[-1].this.rhs.apply(algebra.gt_zero.eq.given.et.div)

    Eq <<= Eq[-2].this.lhs.apply(algebra.lt_zero.imply.eq.abs), Eq[-1].this.lhs.apply(algebra.gt_zero.imply.eq.abs)

    Eq <<= -Eq[-2].this.lhs, Eq[-1].this.lhs.reversed

    Eq << Eq[-2].this.lhs.reversed

    Eq <<= algebra.infer.given.infer.subs.apply(Eq[-2]), algebra.infer.given.infer.subs.apply(Eq[-1])

    Eq <<= Eq[-2].this.find(Min).apply(algebra.min.to.mul), Eq[-1].this.find(Min).apply(algebra.min.to.mul.max)

    Eq <<= Eq[-2].this.find(clip).defun(), Eq[-1].this.find(clip).defun()

    Eq <<= Eq[-2].this.find(Piecewise).apply(algebra.piece.swap), Eq[-1].this.find(Piecewise).apply(algebra.piece.swap)

    Eq << Eq[-2].this.find(Min).apply(algebra.min.to.piece)

    Eq << Eq[-1].this.find(Max).apply(algebra.max.to.piece.gt)





if __name__ == '__main__':
    run()
# created on 2023-03-26
# updated on 2023-05-18
