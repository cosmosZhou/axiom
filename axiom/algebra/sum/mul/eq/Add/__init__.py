from util import *


@apply
def apply(self):
    mul, *limits = self.of(Sum)
    from Axiom.Algebra.Mul.eq.Add import convert
    add = convert(mul)

    from Axiom.Algebra.Sum.eq.Add import associate
    rhs = associate(Sum, Sum(add, *limits))

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    f, h, g = Function(real=True)
    Eq << apply(Sum[i:n]((f(i) + h(i)) * g(i)))

    Eq << Eq[-1].this.lhs.expr.apply(Algebra.Mul.eq.Add)
    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Add)


if __name__ == '__main__':
    run()

# created on 2020-03-27

from . import st
