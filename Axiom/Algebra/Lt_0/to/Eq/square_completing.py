from util import *


@apply(simplify=False)
def apply(gt_zero, self, z=None):
    a = gt_zero.of(Expr < 0)
    assert a.is_finite
    from Axiom.Sets.is_nonzero.to.Eq.Conj.square_completing import quadratic_coefficient
    z, coeffs = quadratic_coefficient(self, z)

    a = coeffs[1][1]
    b = coeffs[1][0]
    S[~b] = coeffs[0][1]
    c = coeffs[0][0]

    rest = c - b * ~b / a
    z += ~b / a
    return Equal(self, a * z * ~z + rest, evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    z, a, b, c = Symbol(complex=True)
    Eq << apply(a < 0, a * z * ~z + b * z + ~b * ~z + c)

    Eq << Algebra.Lt_0.to.Ne_0.apply(Eq[0])

    Eq << Sets.Lt_0.to.is_real.apply(Eq[0], simplify=None)

    Eq << Sets.Ne_0.is_real.to.In.Union.apply(Eq[-2], Eq[-1])

    Eq << Sets.is_nonzero.to.Eq.Conj.square_completing.apply(Eq[-1], Eq[1].lhs, simplify=None)




if __name__ == '__main__':
    run()
# created on 2023-05-02
# updated on 2023-05-03