from util import *



@apply
def apply(given, index=None, reverse=False):
    p, q = given.of(Imply)
    if index is None:
        if p.is_Equal:
            old, new = p.args
        else:
            eqs = p.of(And)
            for eq in eqs:
                if eq.is_Equal:
                    old, new = eq.args
                    break
    else:
        eqs = p.of(And)
        old, new = eqs[index].of(Equal)

    if reverse:
        old, new = new, old
    q = q._subs(old, new)
    return Imply(p, q)


@prove
def prove(Eq):
    from Axiom import Algebra
    x, y = Symbol(real=True)
    A = Symbol(etype=dtype.real)
    f, g = Function(real=True)

    Eq << apply(Imply(Equal(f(x), x + 1) & Element(x, A), Equal(g(f(x)), y)))

    Eq.suffice, Eq.necessary = Algebra.Iff.of.And.apply(Eq[-1])

    Eq << Eq.suffice.this.lhs.apply(Algebra.Imply_And.to.Imply.And, index=0)

    Eq << Eq[-1].this.lhs.rhs.apply(Algebra.Eq.Cond.to.Cond.subs)

    Eq << Eq.necessary.this.rhs.apply(Algebra.Imply_And.to.Imply.And, index=0)

    Eq << Eq[-1].this.rhs.rhs.apply(Algebra.Eq.Cond.to.Cond.subs, reverse=True)


if __name__ == '__main__':
    run()

# created on 2018-02-06
del Bool
from . import Bool
