from util import *

def swap(ecs, i):
    j = i + 1
    assert j < len(ecs)

    ei, ci = ecs[i]
    ej, cj = ecs[j]

    if cj:
        ecs[-2:] = (ej, ci.invert()), (ei, True)
    else:
        ecs[i:i + 2] = (ej, cj & ci.invert()), (ei, ci)

    return ecs

@apply
def apply(piecewise, i=0):
    [*ecs] = piecewise.of(Piecewise)
    return Equal(piecewise, Piecewise(*swap(ecs, i)), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(k,))
    A, B, C = Symbol(etype=dtype.real[k])
    f, g, h, t = Function(shape=(), real=True)
    Eq << apply(Piecewise((f(x), Element(x, A)), (g(x), Element(x, B)), (h(x), Element(x, C)), (t(x), True)), 1)

    p = Symbol(Eq[0].lhs)
    q = Symbol(Eq[0].rhs)
    Eq << p.this.definition

    Eq << q.this.definition

    Eq << Algebra.Cond_Piece.to.Or.apply(Eq[-1])

    Eq << Eq[-1].this.find(Complement[Complement]).args[1].apply(Sets.Complement.eq.Union.Intersect)

    Eq << Eq[-1].this.find(Complement[Complement[Union]]).apply(Sets.Complement.eq.Union.Intersect)

    Eq << Algebra.Or.to.Eq.Piece.apply(Eq[-1], wrt=q)

    Eq << Eq[-1].subs(Eq[1].reversed).reversed

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.rhs.definition

    Eq << Eq[-1].reversed





if __name__ == '__main__':
    run()
# created on 2018-01-17
# updated on 2023-05-21
