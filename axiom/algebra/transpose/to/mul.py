from util import *


@apply
def apply(self, index=None):
    axis = self.axis
    [*args] = self.of(Transpose[axis][Mul])
    
    if axis == len(self.shape) - 1:
        matrices = []
        vector = []
        coeff = []
        for a in args:
            if not a.shape:
                coeff.append(a)
            elif len(a.shape) == 1:
                vector.append(a)
            else:
                matrices.append(a)
 
        if not matrices:
            return
        
        if index is not None:
            assert args[index] in matrices
        else:
            index = args.index(matrices[0])
        matrix = args[index]
        
        if len(matrices) == 1:
            args[index] = OneMatrix(*matrix.shape)
        else:
            del args[index]

        return Equal(self, matrix.T * Mul(*args).T, evaluate=False)

        


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    a = Symbol(real=True, shape=(n,))
    X, Y = Symbol(real=True, shape=(n, n))
    Eq << apply((a * Y * X).T)

    i = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], i)

    


if __name__ == '__main__':
    run()
# created on 2023-03-18
