from util import *


@apply
def apply(given, wrt=None, reverse=True):
    from axiom.sets.ou.imply.el.piece.two import expr_cond_pair
    or_eqs = given.of(Or)

    return Equal(Piecewise(*expr_cond_pair(Equal, or_eqs, wrt, reverse=reverse)).simplify(), wrt)


@prove
def prove(Eq):
    from axiom import sets, algebra

    k = Symbol(integer=True, positive=True)
    x, p = Symbol(real=True, shape=(k,), given=True)
    A, B = Symbol(etype=dtype.real[k], given=True)
    f, g, h = Function(shape=(k,), real=True)
    Eq << apply(Equal(p, f(x)) & Element(x, A) | Equal(p, g(x)) & Element(x, B - A) | Equal(p, h(x)) & NotElement(x, A | B), wrt=p)

    Eq << Eq[0].this.find(Element[Complement]).apply(sets.el_complement.imply.et, simplify=None)

    Eq << Eq[-1].this.find(NotElement[Union]).apply(sets.notin.imply.et.split.union, simplify=None)

    Eq << Eq[-1].apply(algebra.ou.imply.ou.collect, cond=NotElement(x, A))

    Eq << Eq[-1].this.find(Or).apply(algebra.ou.imply.eq.two, wrt=p)

    Eq << Eq[-1].apply(algebra.ou.imply.eq.two, wrt=p)

    Eq << Eq[-1].reversed

    

    
    


if __name__ == '__main__':
    run()

# created on 2018-01-17
# updated on 2023-05-14
