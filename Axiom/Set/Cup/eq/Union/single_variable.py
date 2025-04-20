from util import *


@apply
def apply(self):
    fx, (x, s) = self.of(Cup)
    return Equal(self, fx.as_multiple_terms(x, s, cls=Cup))


@prove
def prove(Eq):
    from Axiom import Set, Algebra, Logic

    A, B = Symbol(etype=dtype.integer)
    x, y = Symbol(integer=True)
    f, g = Function(etype=dtype.real)
    Eq << apply(Cup[x:B](Piecewise((f(x, y), Element(x, A)), (g(x, y), True))))

    Eq << Set.Eq.given.And.Imp.apply(Eq[0], wrt='y')

    Eq <<= Eq[-2].this.lhs.apply(Set.Any_Mem.of.Mem_Cup), \
    Eq[-1].this.rhs.apply(Set.Mem_Cup.given.Any_Mem)

    Eq <<= Eq[-2].this.lhs.expr.apply(Logic.And.ou.OrAndS.of.Cond_Ite__Ite), \
    Eq[-1].this.rhs.expr.apply(Logic.Cond_Ite__Ite.given.And.ou.OrAndS)

    Eq <<= Eq[-2].this.lhs.apply(Algebra.OrAnyS.of.Any_Or), \
    Eq[-1].this.rhs.apply(Algebra.Any_Or.given.OrAnyS)

    Eq <<= Eq[-2].this.lhs.args[0].apply(Algebra.Any.of.Any_And.limits_absorb, index=0), \
    Eq[-1].this.rhs.args[0].apply(Algebra.Any_And.given.Any.limits_absorb, index=0)

    Eq <<= Eq[-2].this.lhs.args[1].apply(Algebra.Any.of.Any_And.limits_absorb, index=1), \
    Eq[-1].this.rhs.args[1].apply(Algebra.Any_And.given.Any.limits_absorb, index=1)

    Eq <<= Eq[-2].this.rhs.apply(Set.Mem_Union.given.OrMemS, simplify=None), \
    Eq[-1].this.lhs.apply(Set.Or.of.Mem_Union, simplify=None)

    Eq <<= Eq[-2].this.rhs.find(Element).apply(Set.Mem_Cup.given.Any_Mem), \
    Eq[-1].this.lhs.find(Element).apply(Set.Any_Mem.of.Mem_Cup)

    Eq << Eq[-2].this.rhs.find(Element).apply(Set.Mem_Cup.given.Any_Mem)

    Eq << Eq[-1].this.lhs.find(Element).apply(Set.Any_Mem.of.Mem_Cup)





if __name__ == '__main__':
    run()

# created on 2018-10-03
# updated on 2023-05-20
