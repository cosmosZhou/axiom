from util import *



@apply
def apply(given, t):
    e, finiteset = given.of(Element)

    args = finiteset.of(FiniteSet)

    finiteset = finiteset.func(*(arg + t for arg in args))

    return Element(e + t, finiteset)


@prove
def prove(Eq):
    from Axiom import Sets

    x = Symbol(integer=True)
    a, b, t = Symbol(real=True)
    Eq << apply(Element(x, {a, b}), t)

    Eq << Sets.In.to.Or.split.FiniteSet.two.apply(Eq[0], simplify=None)

    Eq << Eq[-1].this.args[0] + t

    Eq << Eq[-1].this.args[0] + t

    Eq << Sets.Or_Eq.to.In.FiniteSet.apply(Eq[-1])




if __name__ == '__main__':
    run()

# created on 2021-03-04
# updated on 2023-05-13