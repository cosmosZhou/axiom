from util import *


@apply
def apply(self):
    (x, (S[x], cond, baseset)), B = self.of(Complement[Cup[FiniteSet], Basic])
    return Equal(self, conditionset(x, cond, baseset - B))


@prove
def prove(Eq):
    from Axiom import Set
    A, B = Symbol(etype=dtype.integer)
    x = Symbol(integer=True)
    f = Function(integer=True)

    Eq << apply(conditionset(x, f(x) > 0, A) - B)

    Eq << Set.Eq.given.And.Imp.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Set.Mem.et.NotMem.of.Mem_SDiff, simplify=None), \
    Eq[-1].this.rhs.apply(Set.Mem_SDiff.given.And, simplify=None)

    Eq <<= Eq[-2].this.lhs.find(Element).simplify(), Eq[-1].this.rhs.find(Element).simplify()

    Eq <<= Eq[-2].this.rhs.simplify(), Eq[-1].this.lhs.simplify()


if __name__ == '__main__':
    run()

# created on 2020-11-17
from . import Eq_odd
