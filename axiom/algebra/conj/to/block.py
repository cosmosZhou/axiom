from util import *


@apply
def apply(self):
    from axiom.geometry.sin.to.block import rewrite
    return Equal(self, rewrite(Conjugate, self))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    A, B, C, D = Symbol(complex=True, shape=(n, n))
    Eq << apply(Conjugate(BlockMatrix([[A, B], [C, D]]), evaluate=False))

    i = Symbol(domain=Range(n * 2))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], i)

    

    


if __name__ == '__main__':
    run()
# created on 2023-09-18
