from util import *


def rewrite(cls, self):
    arg = self.of(cls)
    if arg and arg.is_BlockMatrix:
        args = arg.args
        axis = arg.axis
        shape = arg.shape
        return BlockMatrix(*(rewrite(cls, cls(arg)) for arg in args), axis=axis, shape=shape)
    return self

@apply
def apply(self):
    return Equal(self, rewrite(Sin, self))


@prove
def prove(Eq):
    from axiom import algebra, geometry

    n = Symbol(integer=True, positive=True)
    A, B, C, D = Symbol(real=True, shape=(n, n))
    Eq << apply(Sin(BlockMatrix([[A, B], [C, D]])))

    i = Symbol(domain=Range(n * 2))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], i)

    j = Symbol(domain=Range(n * 2))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], j)

    Eq << Eq[-1].this.lhs.apply(geometry.sin.to.piece)

    Eq << Eq[-1].this.find(Sin[Piecewise]).apply(geometry.sin.to.piece)

    Eq << Eq[-1].this.find(Sin[Piecewise]).apply(geometry.sin.to.piece, simplify=0)

    


if __name__ == '__main__':
    run()
# created on 2023-06-08
