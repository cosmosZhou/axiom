from util import *


@apply(simplify=False)
def apply(self, simplify=True):
    from axiom.sets.el_union.then.ou import split
    return split(self, simplify=simplify)


@prove
def prove(Eq):
    from axiom import sets, algebra

    e = Symbol(integer=True, given=True)
    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Element(e, A | B))

    Eq <<= ~Eq[0] & Eq[1]

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin.then.et.split.union, simplify=None)

    Eq << algebra.et.then.ou.apply(Eq[-1])





if __name__ == '__main__':
    run()

# created on 2018-01-10
# updated on 2023-05-20
