from util import *


@apply
def apply(self):
    a, b = self.of((Identity * Expr) @ Expr)

    return Equal(self, a * b)


@prove
def prove(Eq):
    from axiom import discrete

    n = Symbol(domain=Range(2, oo))
    a, b = Symbol(shape=(n,))
    Eq << apply((Identity(n) * a) @ b)

    Eq << Eq[0].this.lhs.apply(discrete.matmul.to.lamda)


if __name__ == '__main__':
    run()
# created on 2023-09-18
