from util import *


@apply
def apply(self):
    x = self.of(sin[Expr * Identity])
    return Equal(self, Identity(self.shape[-1]) * sin(x), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra, Geometry

    x = Symbol(complex=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(sin(x * Identity(n)))

    i = Symbol(domain=Range(n))
    Eq << Algebra.Eq.given.Eq.getitem.apply(Eq[0], i)

    j = Symbol(domain=Range(n))
    Eq << Algebra.Eq.given.Eq.getitem.apply(Eq[-1], j)

    Eq << Eq[-1].this.lhs.apply(Geometry.Sin.eq.Mul.Delta)




if __name__ == '__main__':
    run()
# created on 2023-06-08
