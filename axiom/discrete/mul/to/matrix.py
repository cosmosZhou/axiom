from util import *


@apply
def apply(self):
    for i, matrix in enumerate(self.args):
        if isinstance(matrix, Matrix):
            break
    else:
        return
    
    args = [*self.args]
    args[i] = 1
    factor = Mul(*args)
    assert not factor.shape
    return Equal(self, Matrix(tuple(b * factor for b in matrix.args)))


@prove
def prove(Eq):
    from axiom import algebra

    a, b, c, d = Symbol(real=True)
    x = Symbol(real=True)
    Eq << apply(Matrix((a, b, c, d)) * x)

    j = Symbol(domain=Range(4))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], j)

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.piece)

    


if __name__ == '__main__':
    run()
# created on 2022-07-08
