from util import *


@apply
def apply(n, u=None):
    from axiom.discrete.imply.all_et.mapping.Qu2v import predefined_symbols
    Q, *_ = predefined_symbols(n)
    if u is None:
        u = Q.definition.variable
    return Unequal(Q[u], Q[u].etype.emptySet)


@prove
def prove(Eq):
    from axiom import discrete, sets, algebra

    n = Symbol(integer=True, positive=True, given=True)
    Eq << apply(n)

    i = Symbol(integer=True)
    Q, t = Eq[0].lhs.args
    _t = t.copy(domain=Range(n + 1))
    a = Symbol(Lamda[i:n + 1](i) @ SwapMatrix(n + 1, n, _t))
    Eq << a.this.definition

    Eq << a[n].this.definition.this.rhs.apply(discrete.matmul.to.sum)

    Eq << discrete.cup.finiteset.matmul.apply(a)

    Eq << Eq[-1].this.lhs.apply(sets.cup.limits.domain_defined.insert)

    Eq <<= Eq[-1] & Eq[-3]

    x = Eq[0].rhs.variable.base
    Eq.plausible = Any[x[:n + 1]](Element(x[:n + 1], Q[_t]), plausible=True)

    Eq << Eq.plausible.this.expr.rhs.definition

    Eq << algebra.any.given.any.subs.apply(Eq[-1], x[:n + 1], a, simplify=None)

    Eq << algebra.any.given.cond.apply(Eq[-1])

    Eq << Eq[-1].this.args[0].apply(sets.el.given.subset.cup.finiteset)

    Eq << Eq[-1].this.args[1:].apply(algebra.et.given.et.subs.eq)

    Eq << sets.any_el.imply.ne_empty.apply(Eq.plausible)
    Eq << algebra.cond.imply.all.apply(Eq[-1], _t)
    
    


if __name__ == '__main__':
    run()
# created on 2020-11-07
# updated on 2022-09-20
