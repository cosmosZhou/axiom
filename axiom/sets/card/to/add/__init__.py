from util import *


@apply
def apply(self, index=-1):
    [*args] = self.of(Card[Union])
    import std
    A, B = std.array_split(args, index)
    A = Union(*A)
    B = Union(*B)
    return Equal(self, Card(A - B) + Card(B))


@prove
def prove(Eq):
    from axiom import sets

    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Card(A | B))

    C = Symbol(A - B)
    Eq << Equal(C & B, B.etype.emptySet, plausible=True)

    Eq << Eq[-1].subs(C.this.definition)

    Eq << sets.intersect_is_empty.imply.eq.apply(Eq[-1])

    Eq << Eq[-1].subs(C.this.definition)

    
    


if __name__ == '__main__':
    run()

# created on 2020-07-05
# updated on 2023-06-01
from . import split
