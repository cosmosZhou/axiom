from util import *


@apply
def apply(eq):
    (x, (hx, fx)), gx = eq.of(Equal[Symbol + Mul[sigmoid]])
    assert x.is_symbol
    assert gx._has(x) and fx._has(x) and hx._has(x)
    [n] = x.shape
    return Equal(
        Derivative[x](gx),
        Identity(*x.shape) +  Derivative[x](fx) * (sigmoid(fx) * (1 - sigmoid(fx)) * OneMatrix(n, n)).T * hx + sigmoid(fx) * Derivative[x](hx))


@prove
def prove(Eq):
    from axiom import calculus

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    f, g, h = Function(real=True, shape=(n,))
    Eq << apply(Equal(g(x), x + h(x) * sigmoid(f(x))))

    Eq << calculus.eq.imply.eq.grad.apply(Eq[0], (x,))

    Eq << Eq[-1].this.rhs.apply(calculus.grad.to.add)

    Eq << Eq[-1].this.find(Derivative[sigmoid]).apply(calculus.grad_sigmoid.to.mul.sigmoid.vector)







if __name__ == '__main__':
    run()
# created on 2021-12-22
# updated on 2023-03-18
