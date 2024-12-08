from util import *


@apply
def apply(n, u=None):
    from Axiom.Discrete.All_And.mapping.Qu2v import predefined_symbols
    Q, *_ = predefined_symbols(n)
    if u is None:
        u = Q.definition.variable
    return Unequal(Q[u], Q[u].etype.emptySet)


@prove
def prove(Eq):
    from Axiom import Discrete, Sets, Algebra

    n = Symbol(integer=True, positive=True, given=True)
    Eq << apply(n)

    i = Symbol(integer=True)
    Q, t = Eq[0].lhs.args
    _t = t.copy(domain=Range(n + 1))
    a = Symbol(Lamda[i:n + 1](i) @ SwapMatrix(n + 1, n, _t))
    Eq << a.this.definition

    Eq << a[n].this.definition.this.rhs.apply(Discrete.Dot.eq.Sum)

    Eq << Discrete.Cup.FiniteSet.Dot.apply(a)

    Eq << Eq[-1].this.lhs.apply(Sets.Cup.limits.domain_defined)

    Eq <<= Eq[-1] & Eq[-3]

    x = Eq[0].rhs.variable.base
    Eq.plausible = Any[x[:n + 1]](Element(x[:n + 1], Q[_t]), plausible=True)

    Eq << Eq.plausible.this.expr.rhs.definition

    Eq << Algebra.Any.of.Any.subs.apply(Eq[-1], x[:n + 1], a, simplify=None)

    Eq << Algebra.Any.of.Cond.apply(Eq[-1])

    Eq << Eq[-1].this.find(Element).apply(Sets.In.of.Subset.Cup.FiniteSet)

    Eq << Eq[-1].this.args[1:].apply(Algebra.Eq.Cond.of.And.subs)

    Eq << Sets.Any_In.to.Ne_EmptySet.apply(Eq.plausible)

    Eq << Algebra.Cond.to.All.apply(Eq[-1], _t)





if __name__ == '__main__':
    run()
# created on 2020-11-07
# updated on 2023-08-26
