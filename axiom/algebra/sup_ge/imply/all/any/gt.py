from util import *


@apply
def apply(given, M=None):
    (fx, *limits), M0 = given.of(Sup >= Expr)

    variables = {x for x, *_ in limits}
    if M is None:
        M = given.generate_var(variables, real=True, var='M')
    elif isinstance(M, str):
        M = given.generate_var(variables, real=True, var=M)

    return All[M:Interval.open(-oo, M0)](Any(fx > M, *limits))


@prove
def prove(Eq):
    from axiom import algebra

    M0, a, b = Symbol(real=True, given=True)
    M, x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Sup[x:a:b](f(x)) >= M0)

    Eq << ~Eq[1]

    Eq << Eq[-1].this.expr.apply(algebra.all_le.imply.sup_le)

    Eq << algebra.cond.any.imply.any.et.apply(Eq[0], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.le.ge.imply.ge.transit)
    Eq << algebra.any.imply.any.et.limits.unleash.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2019-04-10
# updated on 2021-09-30