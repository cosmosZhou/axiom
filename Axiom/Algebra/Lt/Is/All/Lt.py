from util import *


@apply
def apply(lt, var=None):
    lhs, rhs = lt.of(Less)
    assert lhs.shape
    if var is None:
        var = lt.generate_var(integer=True)
    return All[var:lhs.shape[0]](lhs[var] < rhs[var])


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n,), real=True)
    Eq << apply(x < y)

    Eq << Eq[0].this.rhs.apply(Algebra.All_Lt.Is.Lt.Lamda)


if __name__ == '__main__':
    run()
# created on 2022-03-31
