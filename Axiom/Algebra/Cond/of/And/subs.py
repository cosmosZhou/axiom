from util import *


@apply
def apply(f_eq, old, new, reverse=False, simplify=True, assumptions={}):
    from Axiom.Algebra.All_Eq.Cond.to.All.subs import subs
    if reverse:
        old, new = new, old
    return subs(f_eq, old, new, simplify=simplify, assumptions=assumptions), Equal(old, new)


@prove
def prove(Eq):
    from Axiom import Algebra

    m, n = Symbol(integer=True, positive=True)
    a, b, c = Symbol(real=True, shape=(m, n))
    S = Symbol(etype=dtype.real[m][n])
    Eq << apply(Element(a * b, S), a, 2 * c)

    Eq << Algebra.Eq.Cond.to.Cond.subs.apply(Eq[2].reversed, Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-03-16
