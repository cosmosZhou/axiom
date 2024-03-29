from util import *


@apply
def apply(self, index=-1):
    x, y = std.array_split(self.of(Sinh[Add]), index)
    x, y = Add(*x), Add(*y)
    return Equal(self, sinh(x) * cosh(y) + cosh(x) * sinh(y))


@prove
def prove(Eq):
    from axiom import geometry

    x, y = Symbol(real=True)
    Eq << apply(sinh(x + y))

    Eq << Eq[0].this.lhs.apply(geometry.sinh.to.sub.exp)

    Eq << Eq[-1].this.rhs.find(Cosh).apply(geometry.cosh.to.add.exp)

    Eq << Eq[-1].this.rhs.find(Cosh).apply(geometry.cosh.to.add.exp)

    Eq << Eq[-1].this.rhs.find(Sinh).apply(geometry.sinh.to.sub.exp)

    Eq << Eq[-1].this.rhs.find(Sinh).apply(geometry.sinh.to.sub.exp)

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1].this.lhs.expand()

    # https://baike.baidu.com/item/%E5%92%8C%E8%A7%92%E5%85%AC%E5%BC%8F



if __name__ == '__main__':
    run()
# created on 2023-11-26

del exp
