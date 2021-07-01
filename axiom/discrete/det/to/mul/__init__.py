from util import *


@apply
def apply(self, doit=True):
    args = self.of(Det[MatMul])
    args = [Det(arg) for arg in args]
    if doit:
        args = [arg.doit() for arg in args]
    
    return Equal(self, Mul(*args))


@prove
def prove(Eq):
    from axiom import discrete

    n = Symbol.n(integer=True, positive=True)
    A = Symbol.A(shape=(n, n), complex=True)
    B = Symbol.B(shape=(n, n), complex=True)
    C = Symbol.C(shape=(n, n), complex=True)
    Eq << apply(Det(A @ B @ C))

    D = Symbol.D(A @ B)
    Eq << Eq[0].subs(D.this.definition.reversed)

    Eq << Eq[-1].this.lhs.apply(discrete.det.to.mul.two)

    Eq << Eq[-1].this.lhs.args[1].arg.definition

    Eq << Eq[-1].this.find(Det[MatMul]).apply(discrete.det.to.mul.two)


if __name__ == '__main__':
    run()
from . import two