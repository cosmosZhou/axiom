from util import *


@apply(simplify=False)
def apply(gt_zero, eq_conj, self, z=None):
    a = gt_zero.of(Expr > 0)
    assert a.is_finite
    b_quote, b_bar = eq_conj.of(Equal)
    b = ~b_bar
    from axiom.sets.is_nonzero.imply.eq.square_completing import quadratic_coefficient
    z, coeffs = quadratic_coefficient(self, z)

    S[a] = coeffs[1][1]
    try:
        S[b] = coeffs[1][0]
        S[b_quote] = coeffs[0][1]
    except Exception as e:
        print('try to prove:')
        print('Equal(%s, %s, plausible=True)' % (coeffs[0][1], ~coeffs[1][0]))
        raise e

    c = coeffs[0][0]

    rest = c - b * ~b / a
    z += ~b / a
    return Equal(self, a * z * ~z + rest, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    z, a, b, b_quote, c = Symbol(complex=True)
    Eq << apply(a > 0, Equal(b_quote, ~b), a * z * ~z + b * z + b_quote * ~z + c)

    Eq << algebra.gt_zero.imply.eq.square_completing.apply(Eq[0], Eq[2].lhs._subs(b_quote, ~b))

    Eq << Eq[2].subs(Eq[1])

    Eq << algebra.et.given.et.apply(Eq[-1], None, simplify=None)

    Eq << algebra.gt_zero.imply.ne_zero.apply(Eq[0])

    Eq << algebra.ne_zero.imply.ne_zero.conj.apply(Eq[-2])

    
    


if __name__ == '__main__':
    run()
# created on 2023-05-02
# updated on 2023-05-03
