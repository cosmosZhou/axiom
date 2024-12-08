from util import *



@apply
def apply(self):
    image_set = self.image_set()
    variables, expr, base_set = image_set

    if isinstance(base_set, Symbol):
        return All(Element(expr, self), (variables, base_set))

@prove
def prove(Eq):
    from Axiom import Sets, Algebra
    e = Symbol(etype=dtype.integer.set)
    s = Symbol(etype=dtype.integer.set.set)
    f = Function(etype=dtype.integer.set)
    S = Symbol(imageset(e, f(e), s))
    Eq << apply(S)

    Eq << Algebra.All.of.Imply.apply(Eq[1])

    Eq << Eq[-1].this.lhs.apply(Sets.In.to.In.Imageset, f)

    Eq << Eq[-1].this.rhs.rhs.definition


if __name__ == '__main__':
    run()

# created on 2020-08-13
