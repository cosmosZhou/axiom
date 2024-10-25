from util import *


@apply
def apply(self, scale):
    scale = sympify(scale)
    assert scale.is_nonzero
    fi, *limits = self.of(Product)
    size = 0
    for x, *ab in limits:
        if ab:
            a, b = ab
            size += b - a
        else:
            return

    fi = fi * scale
    return Equal(self, Product(fi, *limits) / scale ** size)


@prove
def prove(Eq):
    from axiom import algebra

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    f, h = Function(real=True)
    Eq << apply(Product[i:n](f(i) / 2 - h(i)), 2)

    Eq << Eq[0].subs(n, n + 1)

    Eq << Eq[-1].this.lhs.apply(algebra.prod.to.mul.pop)

    Eq << Eq[-1].this.rhs.find(Product).apply(algebra.prod.to.mul.pop)

    Eq << Eq[-1].this.find(Pow).apply(algebra.pow.to.mul.split.exponent)

    Eq << Eq[-1].this.rhs.args[::2].simplify()

    Eq << Eq[0] * Eq[-1].find(Add)

    Eq << Infer(Eq[0], Eq[1], plausible=True)

    Eq << algebra.infer.then.cond.induct.apply(Eq[-1], n, 0)


if __name__ == '__main__':
    run()
# created on 2023-06-03
