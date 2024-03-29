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

    Eq << Derivative[x](log(softmax(f(x)))).this.find(softmax).apply(keras.softmax.to.mul.reducedSum)

    Eq << Eq[-1].this.rhs.apply(calculus.grad.to.add)

    Eq << Eq[-1].T

    Eq << Eq[-1].this.find(Derivative[ReducedSum]).apply(calculus.grad.to.reducedSum)

    j = Symbol(integer=True)
    Eq << Eq[-1].this.find(ReducedSum).apply(algebra.reducedSum.to.sum, j)

    Eq << Eq[-1].this.find(Sum[Mul[~Derivative]]).apply(calculus.grad.to.lamda.mul)

    Eq << Eq[-1].this.find(Mul[Lamda]).apply(algebra.mul.to.lamda)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.lamda)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.domain_defined)

    Eq << Eq[-1].this.find(Sum).doit()

    Eq << Eq[-1].this.find(Lamda)().find(And).simplify()

    Eq << Eq[-1].this.find(Lamda).apply(calculus.lamda.grad.to.matmul)

    Eq << Eq[-1].this.find(Exp).apply(keras.exp.to.mul.softmax)

    Eq << Eq[-1].this.find(Derivative).doit()

    Eq << Eq[-1] * Eq[-1].find(Softmax)

    Eq << Eq[-1].T




if __name__ == '__main__':
    run()
# created on 2023-03-19


from . import using
