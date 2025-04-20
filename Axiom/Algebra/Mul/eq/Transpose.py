from util import *


@apply
def apply(self):
    try:
        A, B = self.of(Transpose * Transpose)
        assert A.shape == B.shape
        return Equal(self, Transpose(A * B, evaluate=False), evaluate=False)
    except:
        A, B = self.of(Transpose / Transpose)
        assert A.shape == B.shape
        return Equal(self, Transpose(A / B, evaluate=False), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True, positive=True)
    A, B = Symbol(real=True, shape=(n, n))
    Eq << apply(A.T * B.T)

    i = Symbol(domain=Range(n))
    Eq << Algebra.Eq.given.Eq.getitem.apply(Eq[0], i)












if __name__ == '__main__':
    run()
# created on 2023-03-18
