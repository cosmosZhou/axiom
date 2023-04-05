from util import *


@apply
def apply(self):
    fx, (x, S[1]) = self.of(Derivative[sigmoid])
    [n] = x.shape
    return Equal(self, (sigmoid(fx) * (1 - sigmoid(fx)) * OneMatrix(n, n)).T * Derivative[x](fx).doit())


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    f = Function(real=True)
    Eq << apply(Derivative[x](sigmoid(f(x))))

    Eq << Eq[0].this.lhs.expr.defun()

    Eq << sigmoid(f(x)).this.defun()

    Eq << (1 - sigmoid(f(x))).this.find(sigmoid).defun()

    Eq << Eq[-1] * Eq[-2]

    Eq << Eq[-4].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Add).apply(algebra.add.to.mul.together)

    Eq << Eq[-1].this.lhs.doit()

    Eq << Mul(*Eq[-1].lhs.args[1:]).this.apply(algebra.mul.to.transpose)

    Eq << Eq[-1].this.rhs.apply(algebra.transpose.to.mul, 2)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Mul(*Eq[-1].lhs.args[1:]).this.apply(algebra.mul.to.transpose)

    Eq << Eq[-2].subs(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2022-01-01
# updated on 2023-03-18


from . import using
