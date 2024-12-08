from util import *


@apply
def apply(self):
    fx, (x, s) = self.of(Cup)
    return Equal(self, fx.as_multiple_terms(x, s, cls=Cup))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    A, B = Symbol(etype=dtype.integer)
    x, y = Symbol(integer=True)
    f, g = Function(etype=dtype.real)
    Eq << apply(Cup[x:B](Piecewise((f(x, y), Element(x, A)), (g(x, y), True))))

    Eq << Sets.Eq.of.And.Imply.apply(Eq[0], wrt='y')

    Eq <<= Eq[-2].this.lhs.apply(Sets.In_Cup.to.Any_In), \
    Eq[-1].this.rhs.apply(Sets.In_Cup.of.Any_In)

    Eq <<= Eq[-2].this.lhs.expr.apply(Algebra.Cond_Piece.to.Or), \
    Eq[-1].this.rhs.expr.apply(Algebra.Cond_Piece.of.Or)

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Any_Or.to.OrAnyS), \
    Eq[-1].this.rhs.apply(Algebra.Any_Or.of.OrAnyS)

    Eq <<= Eq[-2].this.lhs.args[0].apply(Algebra.Any_And.to.Any.limits_absorb, index=0), \
    Eq[-1].this.rhs.args[0].apply(Algebra.Any_And.of.Any.limits_absorb, index=0)

    Eq <<= Eq[-2].this.lhs.args[1].apply(Algebra.Any_And.to.Any.limits_absorb, index=1), \
    Eq[-1].this.rhs.args[1].apply(Algebra.Any_And.of.Any.limits_absorb, index=1)

    Eq <<= Eq[-2].this.rhs.apply(Sets.In_Union.of.Or, simplify=None), \
    Eq[-1].this.lhs.apply(Sets.In_Union.to.Or, simplify=None)

    Eq <<= Eq[-2].this.rhs.find(Element).apply(Sets.In_Cup.of.Any_In), \
    Eq[-1].this.lhs.find(Element).apply(Sets.In_Cup.to.Any_In)

    Eq << Eq[-2].this.rhs.find(Element).apply(Sets.In_Cup.of.Any_In)

    Eq << Eq[-1].this.lhs.find(Element).apply(Sets.In_Cup.to.Any_In)





if __name__ == '__main__':
    run()

# created on 2018-10-03
# updated on 2023-05-20
