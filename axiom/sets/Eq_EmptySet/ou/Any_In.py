from util import *



@apply
def apply(S):
    assert S.is_set

    e = S.element_symbol()
    return Any(Element(e, S), (e,)) | Equal(S, e.emptySet)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra
    S = Symbol(etype=dtype.real)

    Eq << apply(S)

    Eq << Eq[-1].apply(Algebra.Cond.of.And.All, cond=Unequal(S, S.etype.emptySet))

    Eq << Eq[-1].this.expr.apply(Sets.Any_In.of.Ne_EmptySet)


if __name__ == '__main__':
    run()

# created on 2018-09-06
