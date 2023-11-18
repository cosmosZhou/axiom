from util import *


@apply
def apply(self, simplify=True):
    fi, *limits = self.of(Product)
    size = 0
    for x, *ab in limits:
        if ab:
            a, b = ab
            size += b - a
        else:
            return

    fi = -fi
    return Equal(self, Product(fi, *limits) * (-1) ** size)


@prove
def prove(Eq):
    from axiom import algebra

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f, h = Function(real=True)
    Eq << apply(Product[i:n](f(i) - h(i)))

    Eq << Eq[0].this.lhs.apply(algebra.prod.to.mul.scale, -1)


if __name__ == '__main__':
    run()
# created on 2023-06-03
