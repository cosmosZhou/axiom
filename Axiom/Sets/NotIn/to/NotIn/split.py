from util import *



@apply
def apply(given, s=None):
    e, S = given.of(NotElement)
    args = S.of(Union)
    if s is None:
        s = args[0]
    else:
        assert s in args

    return NotElement(e, s)


@prove
def prove(Eq):
    from Axiom import Sets

    x = Symbol(integer=True)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(NotElement(x, A | B))

    Eq << Sets.NotIn.to.And.split.Union.apply(Eq[0], simplify=None)




if __name__ == '__main__':
    run()

# created on 2021-06-09