from util import *


@apply
def apply(given, index=-1):
    e, args = given.of(Element[Intersection])
    first = Intersection(*args[:index])
    second = Intersection(*args[index:])
    return And(Element(e, first), Element(e, second))


@prove
def prove(Eq):
    from Axiom import Algebra, Set, Logic

    e = Symbol(integer=True, given=True)
    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Element(e, A & B))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Set.And.of.Mem_Inter), Eq[-1].this.lhs.apply(Set.Mem.Inter.of.Mem.Mem)




if __name__ == '__main__':
    run()
# created on 2022-01-01

