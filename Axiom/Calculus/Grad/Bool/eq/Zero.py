from util import *


@apply
def apply(self):
    expr, *limits_d = self.of(Derivative[Bool])
    return Equal(self, 0)


@prove
def prove(Eq):
    from Axiom import Algebra, Calculus

    x = Symbol(real=True)
    p = Function(bool=True)
    Eq << apply(Derivative[x](Bool(p(x))))

    Eq << Eq[0].this.find(Bool).apply(Algebra.Bool.eq.Piece)

    Eq << Eq[-1].this.lhs.apply(Calculus.Grad.eq.Piece)




if __name__ == '__main__':
    run()
# created on 2023-06-21
