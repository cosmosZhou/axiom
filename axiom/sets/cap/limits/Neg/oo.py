from util import *


@apply
def apply(self):
    expr, (i,) = self.of(Cap)
    return Equal(self, Cap[i](expr._subs(i, -i)), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    i = Symbol(integer=True)
    f = Function(etype=dtype.real)
    Eq << apply(Cap[i](f(i)))

    Eq << Sets.Eq.of.And.Imply.apply(Eq[-1])

    Eq <<= Eq[-2].this.lhs.apply(Sets.In_Cap.to.All_In, simplify=None), Eq[-1].this.lhs.apply(Sets.In_Cap.to.All_In, simplify=None)

    Eq <<= Eq[-2].this.rhs.apply(Sets.In_Cap.of.All_In, simplify=None), Eq[-1].this.rhs.apply(Sets.In_Cap.of.All_In, simplify=None)

    Eq <<= Eq[-2].this.lhs.apply(Algebra.All.to.All.limits.Neg, simplify=None), Eq[-1].this.lhs.apply(Algebra.All.to.All.limits.Neg, simplify=None)


if __name__ == '__main__':
    run()
# created on 2021-01-23
