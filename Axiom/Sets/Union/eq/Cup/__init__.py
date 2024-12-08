from util import *


@apply
def apply(self):
    from Axiom.Algebra.Add.eq.Sum import piece_together
    return Equal(self, piece_together(Cup, self))


@prove
def prove(Eq):
    from Axiom import Sets

    k, i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f, g = Function(etype=dtype.integer)
    Eq << apply(Cup[j:n, k:n](f(k)) | Cup[i:j, j:k, k:n](g(k)))

    Eq << Eq[0].this.rhs.apply(Sets.Cup.eq.Union)


if __name__ == '__main__':
    run()

# created on 2021-07-13
from . import limits
