from util import *


@apply
def apply(self):
    blocks, *limits = self.of(Lamda[BlockMatrix])
    axis = len(limits)
    vars = self.variables
    
    lamdas = []
    for block in blocks:
        assert not any(s.has(*vars) for s in block.shape)
        
        lamdas.append(Lamda(block, *limits).simplify())
    
    return Equal(self, BlockMatrix[axis](lamdas))

@prove
def prove(Eq):
    from axiom import algebra

    i, j = Symbol(integer=True)
    a, b, m, n = Symbol(integer=True, positive=True)
    f = Function(real=True, shape=(a,))
    g = Function(real=True, shape=(b,))
    Eq << apply(Lamda[j:m, i:n](BlockMatrix(f(i), g(i))))

    i = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)

    j = Symbol(domain=Range(m))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], j)


if __name__ == '__main__':
    run()
# created on 2021-12-30
