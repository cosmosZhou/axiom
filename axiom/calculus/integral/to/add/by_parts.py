from util import *


@apply
def apply(integral, u=None, dv=None):
    [(x, a, b)] = integral.limits
    if u is not None:
        dv = integral.expr / u
        v = integral.func(dv, x).doit()
        du = diff(u, x)
    elif dv is not None:
        u = integral.expr / dv
        v = integral.func(dv, x).doit()
        du = diff(u, x)
    else:
        ...
# u * dv = d(u v) - du * v
    f = (u * v)._eval_interval(x, a, b) - integral.func(du * v, *integral.limits).simplify()
    return Equal(integral, f)


@prove
def prove(Eq):
    from axiom import calculus

    x, a, b = Symbol(real=True)
    u, v = Function(real=True)
    Eq << apply(Integral(u(x) * diff(v(x), x), (x, a, b)), u=u(x))

    @Function(real=True)
    def uv(x):
        return u(x) * v(x)
    
    Eq << diff(uv(x), x).this.expr.defun()

    Eq << Eq[-1].this.rhs.doit()

    Eq << Eq[0] - Eq[0].rhs.args[-1]

    Eq << Eq[-1].this.lhs.apply(calculus.add.to.integral)

    Eq << Eq[-1].subs(Eq[-3].reversed)

    Eq << Eq[-1].this.lhs.doit()

    Eq << Eq[-1].this.lhs.args[-1].defun()

    Eq << Eq[-1].this.lhs.defun()


if __name__ == '__main__':
    run()

# created on 2020-06-07
