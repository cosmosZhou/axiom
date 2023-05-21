from util import *


def of_continuous(cond):
    (limit, fxi), (xi, domain) = cond.of(All[Equal])
    fz, (z, S[xi], S[0]) = limit.of(Limit)
    assert fz._subs(z, xi) == fxi
    assert domain.is_closed
    return fz, (z, *domain.args)


def of_differentiable(cond, open=True, extended=False):
    if open:
        (derivative, R), (x, a, b) = cond.of(All[Element])
    else:
        (derivative, R), (x, domain) = cond.of(All[Element])
        a, b = domain.args
        assert domain.is_closed

    if extended:
        assert R in ExtendedReals
    else:
        assert R in Reals

    fx, (S[x], S[1]) = derivative.of(Derivative)
    return fx, (x, a, b)


def is_differentiable(f, a, b, x=None, open=True, plausible=None, extended=False):
    if x is None:
        x = Symbol(real=True)

    if open:
        left_open = right_open = True
    else:
        left_open = right_open = False

    kwargs = {}
    if plausible:
        kwargs['plausible'] = plausible

    if extended:
        S = Interval(-oo, oo, left_open=False, right_open=False)
    else:
        S = Reals
    return All[x:Interval(a, b, left_open=left_open, right_open=right_open)](Element(Derivative(f(x), x), S), **kwargs)


@apply
def apply(lt, is_continuous, is_differentiable, equal):
    a, b = lt.of(Less)
    fz, (z, S[a], S[b]) = of_continuous(is_continuous)
    S[fz], S[(z, a, b)] = of_differentiable(is_differentiable)

    S[fz._subs(z, a)], S[fz._subs(z, b)] = equal.of(Equal)

    return Any[z:a:b](Equal(Derivative(fz, z), 0))


@prove(proved=False)
def prove(Eq):
    a, b = Symbol(real=True)
    f = Function(shape=(), real=True)
    from axiom.calculus.all_eq.imply.all.any.eq.intermediate_value_theorem import is_continuous
    Eq << apply(a < b, is_continuous(f, a, b), is_differentiable(f, a, b), Equal(f(a), f(b)))


if __name__ == '__main__':
    run()
# created on 2020-04-03
