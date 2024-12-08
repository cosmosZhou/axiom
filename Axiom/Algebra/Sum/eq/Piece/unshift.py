from util import *


@apply
def apply(self):
    function, (i, a, b) = self.of(Sum)
    assert i.is_integer
    front = function._subs(i, a - 1)
    return Equal(self, Piecewise((Sum[i:a - 1:b](function) - front, b >= a), (0, True)), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    i, n = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Sum[i:1:n](f(i)))

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.eq.Add.split, cond={0})

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=n >= 1)

    Eq <<= Algebra.Imply.of.Imply.subs.Bool.apply(Eq[-2]), Algebra.Imply.of.Imply.subs.Bool.apply(Eq[-1], invert=True)

    Eq << Eq[-1].this.lhs.apply(Algebra.Lt.to.Eq_.Sum.Zero, Eq[-1].find(Sum))

    Eq << Eq[-2].this.find(Element).apply(Sets.In_Range.equ.And)

    Eq << Eq[-1].this.find(Less).reversed

    Eq << Eq[-1].this.find(GreaterEqual).apply(Algebra.Ge.to.Gt.relax, lower=0)

    Eq << Algebra.Imply.of.Imply.subs.Bool.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-03-25
