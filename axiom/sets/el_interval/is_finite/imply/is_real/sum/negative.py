from util import *


@apply
def apply(el, is_finite):
    γ, domain = el.of(Element)
    fk, (k, *cond) = is_finite.of(Sup[Abs] < Infinity)
    if cond:
        S[0], S[oo] = cond
    assert k.is_integer
    S[-1], S[0] = domain.of(Interval)
    assert domain.right_open and domain.left_open

    return Element(Sum[k:0:oo](γ ** k * fk), Interval(-oo, oo))



@prove
def prove(Eq):
    from axiom import sets, algebra

    r = Symbol(shape=(oo,), real=True)
    γ = Symbol(real=True)
    k = Symbol(integer=True)
    Eq << apply(Element(γ, Interval(-1, 0, left_open=True, right_open=True)), Less(Sup[k:0:oo](Abs(r[k])), oo))

    @Function
    def h(k):
        return (-1) ** k * r[k]
    Eq.h_def = h(k).this.defun()

    Eq << Eq.h_def * (-1) ** k

    Eq << Eq[1].subs(Eq[-1].reversed)

    Eq << sets.el.imply.el.neg.apply(Eq[0])

    Eq << sets.el_interval.is_finite.imply.is_real.sum.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << Eq[-1].subs(Eq.h_def)

    Eq << Eq[-1].this.find(Mul).args[::2].apply(algebra.mul.to.pow.mul.base, simplify=None)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.domain_defined, simplify=None)




if __name__ == '__main__':
    run()
# created on 2023-04-16
