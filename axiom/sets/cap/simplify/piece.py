from util import *


@apply
def apply(self):
    (piecewise, gx), limit = self.of(Cap[Union[Piecewise, Basic]])
    ecs = ((e | gx, c) for e, c in piecewise)

    return Equal(self, Piecewise(*ecs).as_multiple_terms(*limit.to_setlimit(), Cap))


@prove
def prove(Eq):
    from axiom import sets
    A, C = Symbol(etype=dtype.integer)

    x = Symbol(integer=True)
    f, h, g = Function(etype=dtype.real)

    Eq << apply(Cap[x:A](Union(Piecewise((f(x), Element(x, C)), (h(x), True)), g(x), evaluate=False)))

    Eq << Eq[0].this.lhs.expr.apply(sets.union.to.piece)

    Eq << Eq[-1].this.lhs.apply(sets.cap.to.intersect.st.piece)


if __name__ == '__main__':
    run()

# created on 2021-01-27
