from util import *


@apply
def apply(given, index=-1):
    e, args = given.of(Element[Intersection])
    first = Intersection(*args[:index])
    second = Intersection(*args[index:])
    return And(Element(e, first), Element(e, second))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    e = Symbol(integer=True, given=True)
    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Element(e, A & B))

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Sets.In_Intersect.to.And), Eq[-1].this.rhs.apply(Sets.In.In.to.In.Intersect)




if __name__ == '__main__':
    run()
# created on 2022-01-01
