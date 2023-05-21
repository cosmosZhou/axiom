from util import *


@apply
def apply(self):
    *sizes, d_x = self.shape
    assert not sizes
    [*args], (x, S[1]) = self.of(Derivative[MatMul])
    S[d_x], = x.shape
    for i, fx in enumerate(args):
        if fx._has(x):
            d_fx, = fx.shape
            break
    else :
        return
    
    fx = Derivative[x](fx)
    assert i in (0, len(args) - 1)
    del args[i]

    assert not any(arg._has(x) for arg in args[i:])

    args.append(fx)

    return Equal(self, MatMul(*args))


@prove
def prove(Eq):
    from axiom import discrete, calculus

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    A = Symbol(real=True, shape=(n,))
    f = Function(real=True)
    Eq << apply(Derivative[x](A @ f(x)))

    Eq << Eq[0].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.find(Mul).apply(calculus.mul.to.grad)

    Eq << Eq[-1].this.rhs.find(Sum).apply(calculus.sum.to.grad)

    Eq << Eq[-1].this.rhs.find(Sum).apply(discrete.sum.to.matmul)

    
    


if __name__ == '__main__':
    run()
# created on 2023-04-07
# updated on 2023-04-08
