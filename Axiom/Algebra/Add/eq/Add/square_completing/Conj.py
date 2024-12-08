from util import *


@apply(simplify=False)
def apply(self, z=None):
    from Axiom.Sets.is_nonzero.to.Eq.Conj.square_completing import quadratic_coefficient
    z, coeffs = quadratic_coefficient(self, z)

    a = coeffs[1][1]
    b = coeffs[1][0]
    S[~b] = coeffs[0][1]
    c = coeffs[0][0]

    assert a.is_real and a.is_nonzero
    rest = c - b * ~b / a
    z += ~b / a
    return Equal(self, a * z * ~z + rest, evaluate=False)


@prove
def prove(Eq):
    from Axiom import Sets

    z, b, c = Symbol(complex=True, given=True)
    a = Symbol(real=True, zero=False)
    Eq << apply(a * z * ~z + b * z + ~b * ~z + c)

    Eq << Unequal(a, 0, plausible=True)

    Eq << Sets.Ne_0.to.In.Union.apply(Eq[-1])

    Eq << Sets.is_nonzero.to.Eq.Conj.square_completing.apply(Eq[-1], Eq[0].lhs, simplify=None)




if __name__ == '__main__':
    run()
# created on 2023-05-02
# updated on 2023-05-03
