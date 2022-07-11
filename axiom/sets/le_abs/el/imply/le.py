from util import *


@apply
def apply(le, contains):
    if le.is_Element:
        le, contains = contains, le

    from axiom.algebra.abs_sum.to.mul.sum import dissect_distance
    dx, dy = le.of(LessEqual)

    yt, x, i, n = dissect_distance(dx)

    S[yt], y_mean = dy.of(Abs[Expr - Expr])

    y_sum, m = y_mean.of(Expr / Expr)

    yj, (j, *ab) = y_sum.of(Sum)
    if ab:
        S[0], S[m] = ab

    y = Lamda[j:m](yj).simplify()

    t, s = contains.of(Element)
    assert s in Range(m)
    assert y[t] == yt

    if yt._has(i):
        i_ = le.generate_var(i, integer=True)
    else:
        i_ = i

    if yt._has(j):
        j_ = le.generate_var(j, integer=True)
    else:
        j_ = j

    return LessEqual(Sum[i_:n]((x[i_] - (Sum[i:n](x[i]) + yt) / (n + 1)) ** 2) + (yt - (Sum[i:n](x[i]) + yt) / (n + 1)) ** 2 + Sum[j_:m]((y[j_] - (Sum[j:m](y[j]) - yt) / (m - 1)) ** 2) - (yt - (Sum[j:m](y[j]) - yt) / (m - 1)) ** 2,
                     Sum[i:n]((x[i] - Sum[i:n](x[i]) / n) ** 2) + Sum[j:m]((y[j] - Sum[j:m](y[j]) / m) ** 2))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    x, y = Function(real=True)
    m = Symbol(domain=Range(2, oo))
    i, j = Symbol(integer=True)
    t = Symbol(integer=True, given=True)
    Eq << apply(abs(y(t) - Sum[i:n](x(i)) / n) <= abs(y(t) - Sum[j:m](y(j)) / m), Element(t, Range(m)))

    t_ = Symbol('t', domain=Range(m))
    Eq << Eq[0]._subs(t, t_).this.apply(algebra.le_abs.imply.le.function, t_)

    Eq << Eq[-1].subs(t_, t)

    Eq << algebra.ou.imply.infer.apply(Eq[-1])

    Eq << Eq[-1].this.apply(algebra.infer.flatten)

    Eq <<= Eq[0] & Eq[1]

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2021-03-23
