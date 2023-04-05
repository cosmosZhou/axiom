from util import *


@apply
def apply(eq):
    (c, b_x, A_x2), f = eq.of(Equal[Add])
    assert f.is_Function
    x = f.arg
    b, S[x] = b_x.of(MatMul)
    S[x], A, S[x] = A_x2.of(MatMul)
    return Equal(Derivative(f, x), (A + A.T) @ x + b)


@prove
def prove(Eq):
    from axiom import calculus

    n = Symbol(integer=True, positive=True)
    x = Symbol(r"\vec x", real=True, shape=(n,))
    f = Function(real=True, shape=())
    c = Symbol(real=True)
    b = Symbol(r"\vec b", real=True, shape=(n,))
    A = Symbol(r"\boldsymbol A", real=True, shape=(n, n))
    Eq << apply(Equal(f(x), c + b @ x + x @ A @ x))

    Eq << calculus.eq.imply.eq.grad.apply(Eq[0], (x,))

    Eq << Eq[-1].this.rhs.apply(calculus.grad.to.add)

    Eq << Eq[-1].this.find(Derivative[MatMul]).apply(calculus.grad.to.expr.st.poly.simple)

    Eq << Eq[-1].this.find(Derivative[MatMul]).apply(calculus.grad.to.expr.st.poly.quadratic)





if __name__ == '__main__':
    run()
# created on 2021-12-25
