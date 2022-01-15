from util import *


@apply
def apply(self):
    assert self.is_ZeroMatrix
    m, n = self.shape
    m = int(m)
    n = int(n)
    array = [[0] * n] * m
    return Equal(self, Matrix(array), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    m = 4
    n = 5
    Eq << apply(ZeroMatrix(4, 5))

    i = Symbol(domain=Range(m))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)







if __name__ == '__main__':
    run()
# created on 2021-10-04
