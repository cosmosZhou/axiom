from util import *


@apply
def apply(self, index=-1):
    args = self.of(Cos[Add])
    x = args[:index]
    y = args[index:]
    x = Add(*x)
    y = Add(*y)
    return Equal(self, cos(x) * cos(y) - sin(x) * sin(y))


@prove
def prove(Eq):
    from axiom import calculus, geometry

    x, y = Symbol(real=True)
    Eq << apply(cos(x + y))

    Eq << Eq[0].this.lhs.apply(geometry.cos.to.add.expi)

    Eq << Eq[-1].this.rhs.find(Cos).apply(geometry.cos.to.add.expi)

    Eq << Eq[-1].this.rhs.find(Cos).apply(geometry.cos.to.add.expi)

    Eq << Eq[-1].this.rhs.find(Sin).apply(geometry.sin.to.add.expi)

    Eq << Eq[-1].this.rhs.find(Sin).apply(geometry.sin.to.add.expi)

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1].this.lhs.expand()

    #https://baike.baidu.com/item/%E5%92%8C%E8%A7%92%E5%85%AC%E5%BC%8F




if __name__ == '__main__':
    run()

# created on 2018-06-15
# updated on 2023-05-17

