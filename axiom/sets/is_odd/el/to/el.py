from util import *


@apply
def apply(is_odd, el):
    n = is_odd.of(Equal[Expr % 2, 1])
    S[n], (a, b) = el.of(Element[Range])

    b -= 1

    return Element(n, imageset(n, 2 * n + 1, Range(a // 2, (b - 1) // 2 + 1)))


@prove
def prove(Eq):
    from axiom import algebra, sets

    a, b, n = Symbol(integer=True)
    Eq << apply(Equal(n % 2, 1), Element(n, Range(a, b + 1)))

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(sets.is_odd.el.imply.el)

    Eq << Eq[-1].this.rhs.apply(sets.el.imply.et.is_odd)


if __name__ == '__main__':
    run()

# created on 2018-05-31
# updated on 2023-05-21
