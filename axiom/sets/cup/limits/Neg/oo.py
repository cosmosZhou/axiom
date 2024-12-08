from util import *


@apply
def apply(self):
    expr, (i,) = self.of(Cup)
    return Equal(self, Cup[i](expr._subs(i, -i)), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    i = Symbol(integer=True)
    f = Function(etype=dtype.real)
    Eq << apply(Cup[i](f(i)))

    Eq << Sets.Eq.of.And.Imply.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Sets.In_Cup.to.Any_In), Eq[-1].this.rhs.apply(Sets.In_Cup.of.Any_In)

    Eq <<= Eq[-2].this.rhs.apply(Sets.In_Cup.of.Any_In), Eq[-1].this.lhs.apply(Sets.In_Cup.to.Any_In)

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Any.to.Any.limits.Neg.oo)

    Eq <<= Eq[-1].this.lhs.apply(Algebra.Any.to.Any.limits.Neg.oo)


if __name__ == '__main__':
    run()
# created on 2018-10-05
