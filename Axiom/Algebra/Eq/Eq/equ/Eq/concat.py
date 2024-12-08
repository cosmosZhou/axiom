from util import *


def unshift(fx, gy, _lhs, _rhs, n, k):
    fx0 = fx._subs(k, -1)
    gx0 = gy._subs(k, -1)

    if fx0 == _lhs and gx0 == _rhs:
        n += 1
        fx = fx._subs(k, k - 1)
        gy = gy._subs(k, k - 1)
    elif fx0 == _lhs[0] and gx0 == _rhs[0]:
        size = _lhs.shape[0]
        n += size
        fx = fx._subs(k, k - size)
        gy = gy._subs(k, k - size)
    else:
        return

    return fx, gy, n


@apply
def apply(eq, eq_historic):
    lhs, rhs = eq.of(Equal)
    _lhs, _rhs = eq_historic.of(Equal)

    if len(lhs.shape) < len(_lhs.shape):
        (lhs, rhs), (_lhs, _rhs) = (_lhs, _rhs), (lhs, rhs)
        eq, eq_historic = eq_historic, eq

    n = lhs.shape[0]
    if lhs.is_Lamda and rhs.is_Lamda and lhs.variable == rhs.variable:
        k = rhs.variable
    else:
        k = eq_historic.generate_var(integer=True)

    fx = lhs[k]
    gy = rhs[k]

    if n.is_finite:
        fxn = fx._subs(k, n)
        gyn = gy._subs(k, n)

        if fxn == _lhs and gyn == _rhs:
            n += 1
        elif _lhs.shape and fxn == _lhs[0] and gyn == _rhs[0]:
            n += _lhs.shape[0]
        else:
            fx, gy, n = unshift(fx, gy, _lhs, _rhs, n, k)
    else:
        fx, gy, n = unshift(fx, gy, _lhs, _rhs, n, k)

    return Equal(Lamda[k:n](fx).simplify(), Lamda[k:n](gy).simplify())


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True, positive=True)
    k = Symbol(integer=True)
    f, g = Function(real=True)
    Eq << apply(Equal(f(n), g(n)), Equal(Lamda[k:n](f(k)), Lamda[k:n](g(k))))

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Eq.Eq.to.Eq.concat, simplify=None)

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.to.And.Eq.split, simplify=None)




if __name__ == '__main__':
    run()
# created on 2023-03-30
# updated on 2023-05-21
