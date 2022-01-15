from util import *


@apply
def apply(self):
    args = []
    for arg in self.of(Mul):
        args.append(arg.of(Exp))

    return Equal(self, Exp(Add(*args)), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    a, b = Symbol(real=True)
    Eq << apply(exp(a) * exp(b))

    Eq << Eq[-1].this.rhs.apply(algebra.exp.to.mul)


if __name__ == '__main__':
    run()
# created on 2018-10-25
