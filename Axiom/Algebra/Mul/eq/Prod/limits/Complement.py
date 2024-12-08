from util import *


@apply
def apply(self):
    from Axiom.Algebra.Add.eq.Sum.limits.Complement import limits_complement
    (function, *limits_a), (S[function], *limits_b) = self.of(Product / Product)

    limits = limits_complement(limits_a, limits_b, function=function)
    return Equal(self, Product(function, *limits), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra
    k = Symbol(integer=True)
    A, B = Symbol(etype=dtype.integer)
    f = Function(integer=True)
    Eq << apply(Product[k:A](f(k)) / Product[k:A & B](f(k)))

    Eq << Eq[0].this.lhs.find(Product).apply(Algebra.Prod.eq.Mul.split, cond=B)


if __name__ == '__main__':
    run()
# created on 2020-02-01
