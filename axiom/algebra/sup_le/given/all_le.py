from util import *


@apply
def apply(le):
    (fx, *limits), M = le.of(Sup <= Expr)
    return All(fx <= M, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    m, M, x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Sup[x:Interval(m, M, left_open=True, right_open=True)](f(x)) <= M)

    Eq << algebra.all_le.imply.sup_le.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-04-10
