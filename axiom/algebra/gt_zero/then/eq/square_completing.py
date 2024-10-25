from util import *


@apply(simplify=False)
def apply(gt_zero, self, z=None):
    a = gt_zero.of(Expr > 0)
    assert a.is_finite
    from axiom.sets.is_nonzero.then.eq.conj.square_completing import quadratic_coefficient
    z, coeffs = quadratic_coefficient(self, z)

    S[a] = coeffs[1][1]
    b = coeffs[1][0]
    S[~b] = coeffs[0][1]
    c = coeffs[0][0]

    if c is None:
        c = 0

    rest = c - b * ~b / a
    z += ~b / a
    return Equal(self, a * z * ~z + rest, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra, sets

    z, a, b, c = Symbol(complex=True)
    Eq << apply(a > 0, a * z * ~z + b * z + ~b * ~z + c)

    Eq << algebra.gt_zero.then.ne_zero.apply(Eq[0])

    Eq << sets.gt_zero.then.is_real.apply(Eq[0], simplify=None)

    Eq << sets.ne_zero.is_real.then.el.union.apply(Eq[-2], Eq[-1])

    Eq << sets.is_nonzero.then.eq.conj.square_completing.apply(Eq[-1], Eq[1].lhs, simplify=None)




if __name__ == '__main__':
    run()
# created on 2023-05-02
# updated on 2023-05-03
