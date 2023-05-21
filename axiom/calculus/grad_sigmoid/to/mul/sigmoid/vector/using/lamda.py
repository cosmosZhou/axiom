from util import *


@apply
def apply(self):
    fx, (x, S[1]) = self.of(Derivative[sigmoid])
    n, = x.shape
    return Equal(self, (sigmoid(fx) * (1 - sigmoid(fx)) * OneMatrix(n, n)).T * Derivative[x](fx).doit())


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    f = Function(real=True)
    Eq << apply(Derivative[x](sigmoid(f(x))))

    Eq << Eq[0].this.lhs.expr.defun()

    i, j = Symbol(integer=True)
    Eq << Derivative[x[i]](sigmoid(f(x[j]))).this.expr.defun()

    Eq << Eq[-1].this.rhs.doit()

    Eq << Eq[-1].this.rhs.apply(algebra.mul_kroneckerDelta.subs, -2)

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (i, 0, n))

    Eq.final = algebra.eq.imply.eq.lamda.apply(Eq[-1], (j, 0, n))

    Eq << Eq.final[j, i]

    Eq << sigmoid(f(x)).this.defun()

    Eq << (1 - sigmoid(f(x))).this.find(sigmoid).defun()

    Eq << Eq[-1] * Eq[-2]

    Eq << Eq[-1].this.rhs.find(Add).apply(algebra.add.to.mul.together)

    Eq << Eq.final.subs(Eq[-1].reversed)

    

    

    

    


if __name__ == '__main__':
    run()
# created on 2023-03-18
