from util import *


@apply
def apply(self):
    from Axiom.Algebra.Sum.eq.Add.pop import rewrite
    return Equal(self, rewrite(Product, self), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Function(real=True)
    Eq << apply(Product[i:n + 1](f(i)))

    Eq << Eq[-1].this.lhs.apply(Algebra.Prod.eq.Mul.split, cond={n})





if __name__ == '__main__':
    run()
# created on 2023-03-22
# updated on 2023-04-23