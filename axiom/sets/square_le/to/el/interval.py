from util import *


@apply
def apply(given):
    abs_x, a = given.of(LessEqual)
    x = abs_x.of(Expr ** 2)
    assert x.is_real
    return Element(x, Interval(-sqrt(a), sqrt(a)))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, a = Symbol(real=True)
    Eq << apply(x ** 2 <= a ** 2)

    Eq << Eq[0].this.rhs.apply(sets.el_interval.to.et)

    Eq << Eq[-1].this.find(GreaterEqual).reversed

    Eq << algebra.iff.of.et.infer.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(algebra.square_le.then.et.le)

    Eq << Eq[-1].this.rhs.apply(algebra.square_le.of.et.le)




if __name__ == '__main__':
    run()
# created on 2023-06-18
