from util import *


@apply
def apply(self):
    A, (p, q) = self.of(Infer[Basic, Infer])
    return Infer(p, Infer(A, q))


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(real=True)
    A, B, C = Symbol(etype=dtype.real)
    Eq << apply(Infer(Element(x, A), Infer(Element(y, B), Element(z, C))))

    Eq << Eq[-1].this.lhs.apply(algebra.infer.flatten)

    Eq << Eq[-1].this.rhs.apply(algebra.infer.flatten)




if __name__ == '__main__':
    run()
# created on 2019-10-06
