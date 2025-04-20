from util import *


@apply
def apply(imply):
    from Axiom.Set.Mem.given.Mem.split.Imageset import subs_limits_with_epitome
    e, S = imply.of(Element)

    image_set = S.image_set()

    variables, expr, base_set = image_set
    e = subs_limits_with_epitome(e, expr)
    if e._has(variables):
        _variables = base_set.element_symbol(e.free_symbols)
        assert _variables.type == variables.type
        expr = expr._subs(variables, _variables)
        variables = _variables
    assert not e._has(variables)
    return Any(Equal(e, expr, evaluate=False), (variables, base_set))


@prove
def prove(Eq):
    from Axiom import Algebra, Set

    x, y = Symbol(integer=True)
    f = Function(integer=True)
    S = Symbol(etype=dtype.integer)
    Eq << apply(Element(y, imageset(x, f(x), S)))

    Eq << Eq[1].simplify()

    Eq << Algebra.All.limits_assert.apply(Eq[1].limits)

    Eq << Eq[-1].this.expr.apply(Set.Mem.Imageset.of.Mem, f=f)

    Eq << Algebra.Any.of.Any_Eq.All.subs.apply(Eq[1].reversed, Eq[-1])
    Eq << Algebra.And.of.And.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-07-30
