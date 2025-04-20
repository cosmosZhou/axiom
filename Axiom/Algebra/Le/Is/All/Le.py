from util import *


@apply
def apply(le, var=None):
    lhs, rhs = le.of(LessEqual)
    assert lhs.shape
    if var is None:
        var = le.generate_var(integer=True)
    return All[var:lhs.shape[0]](lhs[var] <= rhs[var])


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n,), real=True)
    Eq << apply(x <= y)

    Eq << Eq[0].this.rhs.apply(Algebra.All_Le.Is.Le.Lamda)


if __name__ == '__main__':
    run()
# created on 2022-03-31
