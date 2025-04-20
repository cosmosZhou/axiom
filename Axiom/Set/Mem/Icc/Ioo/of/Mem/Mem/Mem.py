from util import *


@apply
def apply(contains0, contains1, contains2):
    w, interval01 = contains0.of(Element)
    interval01.of(Interval[0, 1])
    assert interval01.left_open and interval01.right_open

    x0, s = contains1.of(Element)
    x1, S[s] = contains2.of(Element)
    assert s.is_Interval

    return Element(x0 * w + x1 * (1 - w), s)


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    a, b, x0, x1, w = Symbol(real=True)
    domain = Interval(a, b, left_open=True)
    Eq << apply(Element(w, Interval(0, 1, left_open=True, right_open=True)), Element(x0, domain), Element(x1, domain))

    Eq.w_is_positive, Eq.w1_is_positive = Set.And.of.Mem_Icc.apply(Eq[0])

    Eq.w1_is_positive = -Eq.w1_is_positive + 1

    Eq << Set.Mem.Mul.of.Gt_0.Mem.apply(Eq.w_is_positive, Eq[1])

    Eq << Set.Mem.Mul.of.Gt_0.Mem.apply(Eq.w1_is_positive, Eq[2])

    Eq << Set.Mem.Add.Icc.of.Mem.Mem.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)


if __name__ == '__main__':
    run()
# created on 2020-05-08
