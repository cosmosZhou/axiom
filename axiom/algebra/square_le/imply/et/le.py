from util import *


@apply
def apply(given):
    abs_x, a = given.of(LessEqual)
    x = abs_x.of(Expr ** 2)
    assert x.is_real
    return LessEqual(x, sqrt(a)), LessEqual(-sqrt(a), x)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, a = Symbol(real=True)
    Eq << apply(x ** 2 <= a ** 2)

    Eq << algebra.le.imply.le_zero.apply(Eq[0])

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.mul.st.square_difference)

    Eq << algebra.le_zero.imply.ou.split.mul.apply(Eq[-1])

    Eq << Eq[-1].this.args[0].args[0].apply(algebra.le.transport, lhs=0)

    Eq << Eq[-1].this.args[0].args[1].apply(algebra.ge.transport, lhs=1)

    Eq << Eq[-1].this.args[0].apply(sets.le.ge.imply.el.interval)

    Eq << Eq[-1].this.args[1].args[0].apply(algebra.le.transport, lhs=1)

    Eq << Eq[-1].this.args[1].args[1].apply(algebra.ge.transport, lhs=0)

    Eq << Eq[-1].this.args[1].apply(sets.le.ge.imply.el.interval)

    Eq << Eq[-1].this.rhs.apply(sets.union.to.interval.abs)

    Eq << sets.el_interval.imply.et.apply(Eq[-1])

    Eq << Eq[-1].reversed

    


if __name__ == '__main__':
    run()
# created on 2023-06-18
