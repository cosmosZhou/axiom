from util import *


@apply
def apply(self):
    (A, r), ((S[r], epsilon_less, epsilon_more), S[A]) = self.of(Min[Mul, Mul[clip]])
    ε = (epsilon_more - epsilon_less) / 2
    assert epsilon_more + epsilon_less == 2
    assert 0 < ε < 1
    return Equal(self, Piecewise((Piecewise((A * (1 + ε), r > 1 + ε), (A * r, True)), A >= 0), (Piecewise((A * (1 - ε), r <= 1 - ε), (A * r, True)), True)))


@prove
def prove(Eq):
    from axiom import algebra

    ε = Symbol(domain=Interval(0, 1, left_open=True, right_open=True))
    #0 < ε < 1
    r_t = Symbol(real=True, positive=True)
    A_t = Symbol(real=True)
    Eq << apply(Min(r_t * A_t, clip(r_t, 1 - ε, 1 + ε) * A_t))

    Eq << Eq[-1].lhs.this.apply(algebra.min.clip.to.mul.piece)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.piece)

    Eq << Eq[-1].this.find(Mul[Piecewise]).apply(algebra.mul.to.piece)

    Eq << Eq[-1].this.find(Mul[Piecewise]).apply(algebra.mul.to.piece)




if __name__ == '__main__':
    run()
# created on 2023-03-31
