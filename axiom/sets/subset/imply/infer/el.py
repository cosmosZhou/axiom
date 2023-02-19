from util import *


@apply
def apply(given, x):
    A, B = given.of(Subset)
    return Infer(Element(x, A), Element(x, B))


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol(integer=True, positive=True)
    A, B = Symbol(etype=dtype.integer * n)
    x = Symbol(complex=True, shape=(n,), given=True)
    Eq << apply(Subset(A, B), x)

    Eq << sets.subset.imply.all_el.apply(Eq[0])

    a = Eq[-1].variable
    Eq << algebra.all.imply.infer.apply(Eq[-1])

    Eq << Eq[-1].subs(a, x)

    


if __name__ == '__main__':
    run()
# created on 2022-09-20
