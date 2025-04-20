from util import *


@apply
def apply(self):
    fx, (x, s) = self.of(Cap)
    return Equal(self, fx.as_multiple_terms(x, s, cls=Cap))


@prove
def prove(Eq):
    from Axiom import Set, Algebra, Logic

    A, B = Symbol(etype=dtype.integer)
    x, y = Symbol(integer=True)
    f, g = Function(etype=dtype.real)
    Eq << apply(Cap[x:B](Piecewise((f(x, y), Element(x, A)), (g(x, y), True))))

    Eq << Set.Eq.given.And.Imp.apply(Eq[0], wrt='y')

    Eq <<= Eq[-2].this.lhs.apply(Set.All_Mem.of.Mem_Cap), \
    Eq[-1].this.rhs.apply(Set.Mem_Cap.given.All_Mem)

    Eq <<= Eq[-2].this.lhs.expr.apply(Logic.And.ou.OrAndS.of.Cond_Ite__Ite), \
    Eq[-1].this.rhs.expr.apply(Logic.Cond_Ite__Ite.given.And.ou.OrAndS)

    Eq <<= Eq[-2].this.rhs.apply(Set.Mem_Inter.given.And.Mem, simplify=None), \
    Eq[-1].this.lhs.apply(Set.And.Mem.of.Mem_Inter, simplify=None)

    Eq <<= Eq[-2].this.rhs.find(Element).apply(Set.Mem_Cap.given.All_Mem), \
    Eq[-1].this.lhs.find(Element).apply(Set.All_Mem.of.Mem_Cap)

    Eq <<= Eq[-2].this.rhs.find(Element).apply(Set.Mem_Cap.given.All_Mem), \
    Eq[-1].this.lhs.find(Element).apply(Set.All_Mem.of.Mem_Cap)

    Eq <<= Eq[-2].this.lhs.apply(Algebra.And.All.of.All.split, cond=A), Eq[-1].this.rhs.apply(Algebra.All.given.And.All.split, cond=A)

    Eq <<= Eq[-2].this.lhs.args[0].apply(Logic.All.Is.Imp), Eq[-1].this.rhs.args[0].apply(Logic.All.Is.Imp)

    Eq <<= Eq[-2].this.lhs.args[0].lhs.apply(Set.Mem_Inter.Is.And_MeM_Inter, index=0, simplify=False), \
    Eq[-1].this.rhs.args[0].lhs.apply(Set.Mem_Inter.Is.And_MeM_Inter, index=0, simplify=False)

    Eq <<= Eq[-2].this.lhs.args[0].apply(Logic.Imp.subs.Bool, index=0, invert=True), \
    Eq[-1].this.rhs.args[0].apply(Logic.Imp.subs.Bool, index=0, invert=True)

    Eq <<= Eq[-2].this.lhs.args[0].lhs.args[1].apply(Set.Mem_Inter.Is.And_MeM_Inter), \
    Eq[-1].this.rhs.args[0].lhs.args[1].apply(Set.Mem_Inter.Is.And_MeM_Inter)

    Eq <<= Eq[-2].this.lhs.args[0].apply(Logic.Imp.Is.All, wrt=x), \
    Eq[-1].this.rhs.args[0].apply(Logic.Imp.Is.All, wrt=x)

    Eq <<= Eq[-2].this.lhs.args[1].apply(Logic.All.Is.Imp), Eq[-1].this.rhs.apply(Logic.All.Is.Imp)

    Eq <<= Eq[-2].this.lhs.args[0].lhs.apply(Set.Mem_SDiff.Is.And_NotMem), \
    Eq[-1].this.rhs.lhs.apply(Set.Mem_SDiff.Is.And_NotMem)

    Eq <<= Eq[-2].this.lhs.args[0].apply(Logic.Imp.subs.Bool, index=1, invert=True), \
    Eq[-1].this.rhs.apply(Logic.Imp.subs.Bool, index=1, invert=True)

    Eq <<= Eq[-2].this.lhs.args[0].lhs.simplify(), Eq[-1].this.rhs.lhs.simplify()

    Eq <<= Eq[-2].this.lhs.args[0].apply(Logic.Imp.Is.All, wrt=x), \
    Eq[-1].this.rhs.apply(Logic.Imp.Is.All, wrt=x)




if __name__ == '__main__':
    run()

# created on 2021-01-26
# updated on 2023-04-29
