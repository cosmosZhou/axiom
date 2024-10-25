from util import *


@apply
def apply(self):
    expr, *limits = self.of(Sup)
    return All(LessEqual(expr, self), *limits)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    f = Function(real=True)
    Eq << apply(Sup[x:S](f(x)))

    Eq << algebra.then.all.sup_ge.apply(Eq[0].find(Sup))

    Eq << Eq[-1].this.expr.reversed


if __name__ == '__main__':
    run()
# created on 2023-03-28
