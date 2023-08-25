from util import *


@apply
def apply(self):
    import std
    matrix, scalar = std.array_split(self.of(Det[Mul]), lambda arg: arg.shape)
    scalar = Mul(*scalar)
    matrix = Mul(*matrix)

    n = matrix.shape[-1]
    return Equal(self, scalar ** n * Det(matrix))


@prove
def prove(Eq):
    from axiom import discrete

    n = Symbol(integer=True, positive=True)
    X = Symbol(shape=(n, n), complex=True)
    a = Symbol(complex=True)
    Eq << apply(Det(a * X))

    i = Symbol(integer=True)
    @Function(complex=True)
    def f(i):
        return a

    Eq << (X * Lamda[i:n](f(i))).this.find(f).defun()

    Eq << Eq[0].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.lhs.apply(discrete.det_mul.to.mul.prod)

    Eq << Eq[-1].this.find(f).defun()



if __name__ == '__main__':
    run()
# created on 2020-08-19
from . import prod
# updated on 2022-01-15
