from util import *


@apply
def apply(eq_y, L):
    (x, WT), y = eq_y.of(Equal[MatMul])
    W = WT.T   
    return Equal(Derivative[x](L(x @ W.T)), Derivative[y](L(y)) @ W)


@prove
def prove(Eq):
    from axiom import calculus, discrete

    # seq_length, hidden-size, output-hidden-size
    n, d, h = Symbol(integer=True, positive=True)
    x = Symbol(shape=(n, d), real=True)
    W = Symbol(shape=(h, d), real=True)
    y = Symbol(shape=(n, h), real=True)
    L = Function(shape=(), real=True)
    Eq << apply(
        Equal(y, x @ W.T), L)

    Eq << Eq[1].this.lhs.apply(calculus.grad.to.lamda)

    Eq << Eq[-1].this.rhs.find(Derivative).apply(calculus.grad.to.lamda)

    Eq << Eq[-1].this.lhs.find(MatMul).apply(discrete.matmul.to.lamda, simplify=None)

    
    


if __name__ == '__main__':
    run()
# created on 2024-02-13
# updated on 2024-02-15
