from util import *


@apply
def apply(self):
    from Axiom.Algebra.Sum.doit.inner import doit
    return doit(All, self)


@prove
def prove(Eq):
    from Axiom import Algebra
    x = Symbol(real=True, shape=(oo, oo))
    i, j = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)

    n = 5
    Eq << apply(All[j:n, i:m](x[i, j] > 0))

    Eq << Iff(All[i:m](Equal(Bool(All[j:n](x[i, j] > 0)), 1)), All[j:n, i:m](x[i, j] > 0), plausible=True)

    Eq << Eq[-1].this.find(Bool).apply(Algebra.Bool.eq.Piece)

    Eq << Eq[-1].this.find(Bool, All).apply(Algebra.All.equ.And.doit)

    Eq << Eq[-1].this.find(Bool).apply(Algebra.Bool.eq.Piece)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2018-12-05
from . import setlimit
