from util import *


@apply
def apply(le, le_neg):
    x, y = le.of(LessEqual)
    S[-x], S[y] = le_neg.of(LessEqual)
    return abs(x) <= y


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True)
    Eq << apply(x <= y, -x <= y)

    Eq << Eq[0] - y

    Eq << Eq[1] - y

    Eq << Algebra.Le_0.Le_0.to.Ge_0.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.expand() + x * x

    Eq << Eq[-1].reversed

    Eq.lt = Algebra.Le.to.Le.Sqrt.apply(Eq[-1])

    Eq << Algebra.Le.Ge.to.Ge.trans.apply(Eq[0], -Eq[1])

    Eq << (Eq[-1] + y) / 2

    Eq << Algebra.Ge_0.to.Eq.Abs.apply(Eq[-1])

    Eq << Eq.lt.subs(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2022-01-07
del Mul
from . import Mul
from . import Sub
del Add
from . import Add
