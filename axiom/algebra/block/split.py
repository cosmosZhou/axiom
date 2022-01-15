from util import *


@apply
def apply(self, k):
    args = self.of(BlockMatrix[1])
    assert k >= 0 and k <= self.shape[0], "requirements not satisfied, %s >= 0 and %s <= %s" % (k, k, self.shape[0])
    
    blocks = [None, None]
    blocks[0] = [None] * len(args)
    blocks[1] = [None] * len(args)
    for j, arg in enumerate(args):
        blocks[0][j] = arg[:k]
        blocks[1][j] = arg[k:]
        
    return Equal(self, BlockMatrix(blocks))


@prove
def prove(Eq):
    from axiom import algebra

    m, n0, n1 = Symbol(integer=True, positive=True)
    A = Symbol(real=True, shape=(m, n0))
    B = Symbol(real=True, shape=(m, n1))
    k = Symbol(domain=Range(1, m))
    Eq << apply(BlockMatrix[1]([A, B]), k)

    i = Symbol(domain=Range(m))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)

    

    

    

    

    

    


if __name__ == '__main__':
    run()
# created on 2021-12-30
