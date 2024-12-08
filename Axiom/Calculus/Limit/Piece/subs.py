from util import *


def subs(self, x, x0):
    [*args] = self.args

    if self.is_Piecewise:
        for i, (e, c) in enumerate(args):
            if c:
                continue
            if c._subs(x, oo):
                args[i] = (e, True)
                i += 1
                break
        else:
            return self
        return Piecewise(*args)

    hit = False
    for i, arg in enumerate(self.args):
        arg = subs(arg, x, x0)
        if arg == args[i]:
            continue
        args[i] = arg
        hit = True
    if hit:
        return self.func(*args)

    return self

@apply
def apply(self):
    expr, (x, x0) = self.of(Limit)
    assert x0 == oo
    _expr = subs(expr, x, x0)
    assert _expr != expr
    return Equal(self, Limit[x:x0](_expr))


@prove
def prove(Eq):
    from Axiom import Calculus, Algebra, Sets

    n = Symbol(integer=True)
    a = Symbol(integer=True, given=True)
    f, g = Function(real=True)
    Eq << apply(Limit[n:oo](Piecewise((f(n), n > a), (g(n), True))))

    A = Symbol(Eq[0].rhs, real=True)
    Eq << A.this.definition

    Eq << Calculus.Eq_Limit.to.Any.All.limit_definition.apply(Eq[-1])

    Eq << Eq[0].subs(Eq[1].reversed)

    Eq << Eq[-1].this.apply(Calculus.Eq.equ.Any_All.limit_definition)

    Eq << Eq[-1].this.find(Less).apply(Algebra.Cond_Piece.of.Or)

    Eq << Eq[-1].this.expr.apply(Algebra.All_Or.of.All)

    N = Eq[-1].variable
    Eq << Algebra.Any.of.Any.subs.apply(Eq[-1], N, Max(N, a))

    Eq << Eq[2].this.expr.apply(Algebra.All.to.All.limits.restrict, Range(Max(N + 1, a + 1), oo))

    Eq << Eq[-1].this.find(Max).apply(Algebra.Max.eq.Add)

    Eq << Eq[-1].this.expr.apply(Algebra.All.to.All.And)

    Eq << Eq[-1].this.find(Element).apply(Sets.In_Range.to.And)

    Eq << Eq[-1].this.find(GreaterEqual).apply(Algebra.Ge.to.Gt.relax)

    Eq << Eq[-1].this.find(Greater).apply(Algebra.Gt_Max.to.Gt, 1)




if __name__ == '__main__':
    run()
# created on 2020-05-28
# updated on 2023-04-29
