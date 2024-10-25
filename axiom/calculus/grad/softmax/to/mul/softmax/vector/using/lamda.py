from util import *


@apply
def apply(self):
    fx, (x, S[1]) = self.of(Derivative[softmax])
    n, = x.shape
    dfx = Derivative[x](fx).doit()
    return Equal(self, ((dfx.T - ((dfx @ OneMatrix(n)) * Softmax(fx))) * Softmax(fx)).T)


@prove
def prove(Eq):
    from axiom import keras, calculus, algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    f = Function(real=True)
    Eq << apply(Derivative[x](softmax(f(x))))

    i = Symbol(integer=True)
    Eq << Derivative[x[i]](log(softmax(f(x)))).this.find(softmax).apply(keras.softmax.to.mul.reducedSum)

    Eq << Eq[-1].this.rhs.apply(calculus.grad.to.add)

    Eq << Eq[-1].this.find(Derivative[ReducedSum]).apply(calculus.grad.to.reducedSum)

    Eq << Eq[-1].this.find(ReducedSum).apply(algebra.reducedSum.to.sum)

    Eq << Eq[-1].this.find(Sum[Mul[~Derivative]]).apply(calculus.grad.to.mul.grad)

    Eq << Eq[-1].this(i).find(Element).simplify()

    # using lamda
    Eq << Eq[-1].this.lhs.doit()

    Eq << Eq[-1] * Eq[-1].find(Softmax)

    Eq << algebra.eq.then.eq.lamda.apply(Eq[-1], (i, 0, n))

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.add)

    Eq << Eq[-1].this.find(Exp).apply(keras.exp.to.mul.softmax)

    Eq << Eq[-1].this.find(Lamda).apply(calculus.lamda.grad.to.matmul)

    Eq << Eq[-1].T





if __name__ == '__main__':
    run()
# created on 2023-03-18
# updated on 2023-03-19
