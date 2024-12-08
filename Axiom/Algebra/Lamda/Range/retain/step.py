from util import *


@apply
def apply(self, axis=0):
    expr, *limits = self.of(Lamda)

    i, *ab = limits[axis]
    if len(ab) == 2:
        S[0], stop = ab
        stop, step = stop.of(Ceiling[Expr / Expr])
        try:
            stop, start = stop.of(Expr - Expr)
        except:
            start = 0

        limits[axis] = i, Range(start, stop, step)
        expr = expr._subs(i, (i - start) / step)
    else:
        return
    return Equal(self, Lamda(expr, *limits))


@prove
def prove(Eq):
    from Axiom import Algebra

    d = Symbol(integer=True, positive=True)
    a, b, i = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(Lamda[i:Ceiling((b - a) / d)](f(a + d * i)))

    Eq << Eq[0].this.rhs.apply(Algebra.Lamda.Range.simp)




if __name__ == '__main__':
    run()
# created on 2021-12-28
