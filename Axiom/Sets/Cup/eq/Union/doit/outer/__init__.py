from util import *


@apply
def apply(self):
    from Axiom.Algebra.Sum.eq.Add.doit.outer import doit
    return Equal(self, doit(Cup, self))


@prove
def prove(Eq):
    from Axiom import Sets
    x = Symbol(etype=dtype.real, shape=(oo, oo))
    i, j = Symbol(integer=True)
    f = Function(integer=True)

    n = 5
    Eq << apply(Cup[j:f(i), i:n](x[i, j]))

    s = Symbol(Lamda[i](Cup[j:f(i)](x[i, j])))

    Eq << s[i].this.definition

    Eq << Sets.Eq.to.Eq.Cup.apply(Eq[-1], (i, 0, n))

    Eq << Eq[-1].this.lhs.apply(Sets.Cup.eq.Union.doit).reversed

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition


if __name__ == '__main__':
    run()

# created on 2021-02-23
from . import setlimit
