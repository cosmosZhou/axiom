from util import *


@apply
def apply(given, left=None):
    [*args], rhs = given.of(Equal[MatMul])
    assert rhs.is_invertible
    
    if left:
        X = args.pop(0)
        rhs = X.inverse() @ rhs
    else:
        X = args.pop()
        rhs = rhs @ X.inverse()
    assert X.is_square
    
    return Equal(MatMul(*args), rhs)


@prove
def prove(Eq):
    from axiom import discrete

    n = Symbol(integer=True, positive=True)
    A, B = Symbol(real=True, shape=(n, n))
    C = Symbol(real=True, shape=(n, n), singular=False)
    Eq << apply(Equal(A @ B, C))

    Eq << discrete.eq.imply.eq.inverse.apply(Eq[0])

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], B)

    Eq << discrete.eq.imply.eq.inverse.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-04-30
