from util import *


@apply
def apply(lt, is_finite, n=None):
    λ = lt.of(Abs < 1)
    x = is_finite.of(Abs < Infinity)    
    return Equal(Limit[n:oo](λ ** n * x), ZeroMatrix(*x.shape))


@prove(proved=False)
def prove(Eq):
    x = Symbol(real=True)
    λ = Symbol(real=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(Abs(λ) < 1, Less(Abs(x), oo, evaluate=False), n)

    


if __name__ == '__main__':
    run()
# created on 2023-03-30
