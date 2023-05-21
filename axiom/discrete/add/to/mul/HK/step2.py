from util import *

from axiom.discrete.H.to.add.definition import H
from axiom.discrete.K.to.add.definition import K



@apply
def apply(x):
    n = x.shape[0]
    n -= 1

    return Equal(H(x[:n + 1]) * K(x[:n - 1]) - H(x[:n - 1]) * K(x[:n + 1]), (-1) ** n * x[n])


@prove
def prove(Eq):
    from axiom import discrete

    x = Symbol(integer=True, shape=(oo,))
    n = Symbol(domain=Range(2, oo))
    Eq << apply(x[:n + 1])

    Eq << Eq[-1].this.lhs.args[1].args[2].defun()

    Eq << Eq[-1].this.lhs.args[0].args[0].defun()

    Eq << Eq[-1].this.lhs.expand()

    Eq << discrete.add.to.pow.HK.recurrence.apply(x[:n])

    Eq << Eq[-1] * x[n]

    Eq << Eq[-1].this.lhs.expand()

    


if __name__ == '__main__':
    run()

# created on 2020-08-15
# updated on 2023-05-20
