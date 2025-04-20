from util import *


@apply
def apply(self):
    assert self.is_ConditionSet
    variable, expr, base_set = self.base_set.image_set()
    if base_set.is_bool:
        condition = base_set & self.condition._subs(self.variable, expr)
    else:
        condition = Element(variable, base_set).simplify() & self.condition._subs(self.variable, expr)
    return Equal(self, imageset(variable, expr, conditionset(variable, condition)))


@prove
def prove(Eq):
    from Axiom import Set, Algebra, Logic

    n, m = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    y = Symbol(complex=True, shape=(m,))
    A = Symbol(etype=dtype.complex[n])
    f = Function(complex=True, shape=(m,))
    g = Function(shape=(), real=True)
    s = Symbol(imageset(x, f(x), A))
    Eq << apply(conditionset(y, g(y) > 0, s))

    Eq << Eq[1].this.lhs.limits[0][2].definition

    B = Symbol(Eq[-1].lhs)
    B_quote = Symbol(Eq[-1].rhs)
    Eq << B.this.definition

    Eq << B_quote.this.definition

    Eq.suffice = Imply(Element(y, B), Element(y, B_quote), plausible=True)

    Eq << Eq.suffice.this.rhs.rhs.definition

    Eq << Eq[-1].this.rhs.apply(Set.Mem.given.Any.Eq.split.Imageset)

    Eq << Eq[-1].this.lhs.rhs.definition

    Eq << Eq[-1].this.rhs.apply(Algebra.Any.given.Any.And.limits.unleash)

    Eq << Eq[-1].this.lhs.args[1].apply(Set.Any.Eq.of.Mem.split.Imageset)

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.Eq.Cond.given.And.subs, reverse=True)

    Eq.necessary = Given(Element(y, B), Element(y, B_quote), plausible=True)

    Eq << Eq.necessary.this.rhs.rhs.definition

    Eq << Eq[-1].this.rhs.apply(Set.Any.Eq.of.Mem.split.Imageset)

    Eq << Eq[-1].this.rhs.apply(Algebra.Any.And.of.Any.limits.single_variable)

    Eq << Eq[-1].this.rhs.expr.apply(Logic.Cond.of.Eq.Cond.subs, reverse=True, ret=0)

    Eq << Eq[-1].this.lhs.rhs.definition

    Eq << Eq[-1].this.lhs.args[1].apply(Set.Mem.given.Any.Eq.split.Imageset)

    Eq << Set.Eq.of.Imp.Given.apply(Eq.suffice, Eq.necessary)

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.rhs.definition





if __name__ == '__main__':
    run()

# created on 2021-02-04
# updated on 2023-11-11
