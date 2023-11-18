from util import *


@apply
def apply(is_real, given, epsilon=None, delta=None):

    l, a = given.of(Equal)
    if a.is_Limit:
        l, a = a, l

    S[a], S[Reals] = is_real.of(Element)

    _a = l.generate_var(excludes=l.variable, real=True)
    given = given._subs(a, _a)
    from axiom.calculus.eq.to.any_all.limit_definition import any_all
    given = any_all(given, epsilon, delta)
    return given._subs(_a, a)


@prove
def prove(Eq):
    from axiom import sets, algebra, calculus

    n = Symbol(integer=True, positive=True)
    x, x0 = Symbol(real=True)
    f = Function(real=True, shape=())
    a = Symbol(complex=True)
    Eq << apply(Element(a, Reals), Equal(Limit[x:x0 + S.Infinitesimal](f(x)), a))

    Eq << sets.el.imply.any.eq.apply(Eq[0], var='A')

    Eq << algebra.cond.any.imply.any.et.apply(Eq[1], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs, ret=0)

    Eq << Eq[-1].this.expr.args[1].apply(calculus.eq_limit.imply.any.all.limit_definition)

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs, reverse=True)


if __name__ == '__main__':
    run()
# created on 2020-06-23
