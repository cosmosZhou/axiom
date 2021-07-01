from util import *



# given: A in B
# => {A} subset B
@apply
def apply(given):
    assert given.is_Contains
    e, s = given.args

    return Subset(e.set, s)


@prove
def prove(Eq):
    from axiom import sets
    e = Symbol.e(integer=True)
    s = Symbol.s(etype=dtype.integer)
    Eq << apply(Contains(e, s, evaluate=False))

    Eq << sets.subset.imply.contains.apply(Eq[1])

if __name__ == '__main__':
    run()
