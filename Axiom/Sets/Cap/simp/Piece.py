from util import *


@apply
def apply(self):
    (piecewise, gx), limit = self.of(Cap[Union[Piecewise, Basic]])
    ecs = ((e | gx, c) for e, c in piecewise)

    return Equal(self, Piecewise(*ecs).as_multiple_terms(*limit.to_setlimit(), Cap))


@prove
def prove(Eq):
    from Axiom import Sets
    A, C = Symbol(etype=dtype.integer)

    x = Symbol(integer=True)
    f, h, g = Function(etype=dtype.real)

    Eq << apply(Cap[x:A](Union(Piecewise((f(x), Element(x, C)), (h(x), True)), g(x), evaluate=False)))

    Eq << Eq[0].this.lhs.expr.apply(Sets.Union.eq.Piece)

    Eq << Eq[-1].this.lhs.apply(Sets.Cap.eq.Intersect.st.Piece)


if __name__ == '__main__':
    run()

# created on 2021-01-27
