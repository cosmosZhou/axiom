from util import *


@apply
def apply(self, *, cond=None, wrt=None, simplify=True):
    from Axiom.Algebra.Sum.eq.Add.split import split
    return Equal(self, split(Product, self, cond, wrt=wrt, simplify=simplify), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x = Symbol(integer=True)
    f = Function(real=True)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Product[x:A](f(x)), cond=B)

    Eq << Eq[-1].this.find(Product).apply(Algebra.Prod.Bool)

    Eq << Eq[-1].this.rhs.find(Product).apply(Algebra.Prod.Bool)

    Eq << Eq[-1].this.find(Product[2]).apply(Algebra.Prod.Bool)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.Prod.eq.Prod)

    Eq << Eq[-1].this.rhs.expr.powsimp()

    Eq << Eq[-1].this.find(Element).apply(Sets.In.equ.Or.split, B)

    Eq << Eq[-1].this.find(Bool).apply(Algebra.Bool.eq.Add)




if __name__ == '__main__':
    run()

# created on 2018-04-15
# updated on 2023-05-12
