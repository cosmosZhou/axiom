from util import *


@apply
def apply(self):
    from Axiom.Algebra.All.doit.inner.setlimit import doit
    return doit(Any, self)


@prove
def prove(Eq):
    from Axiom import Algebra, Logic
    x = Symbol(real=True, shape=(oo, oo))
    i, j, a, b, c, d = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)

    Eq << apply(Any[j:{a, b, c, d}, i:m](x[i, j] > 0))

    Eq << Iff(Any[i:m](Equal(Bool(Any[j:{a, b, c, d}](x[i, j] > 0)), 1)), Any[j:{a, b, c, d}, i:m](x[i, j] > 0), plausible=True)

    Eq << Eq[-1].this.find(Bool).apply(Logic.Bool.eq.Ite)

    Eq << Eq[-1].this.find(Bool, Any).apply(Algebra.Any.Is.Or.doit.setlimit)

    Eq << Eq[-1].this.find(Bool).apply(Logic.Bool.eq.Ite)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2019-02-10
