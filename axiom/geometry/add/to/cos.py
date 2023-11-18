from util import *


@apply
def apply(self):
    (x, y), (S[x], S[y]) = self.of(Sin * Sin + Cos * Cos)
    return Equal(self, cos(x - y))


@prove
def prove(Eq):
    from axiom import geometry

    x, y = Symbol(real=True)
    Eq << apply(cos(x) * cos(y) + sin(x) * sin(y))

    Eq << Eq[-1].this.rhs.apply(geometry.cos.to.add)



if __name__ == '__main__':
    run()
# created on 2023-06-01

