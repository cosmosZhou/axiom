from util import *


@apply
def apply(el, is_finite):
    λ, domain = el.of(Element)
    S[-1], S[0] = domain.of(Interval)
    assert domain.right_open and domain.left_open
    
    fn, (n, *cond) = is_finite.of(Sup[Abs] < Infinity)
    if cond:
        S[0], S[oo] = cond
    assert n.is_integer
    return Equal(Limit[n:oo](λ ** n * fn), ZeroMatrix(*fn.shape))



@prove
def prove(Eq):
    from axiom import sets, calculus, algebra

    x = Symbol(real=True, shape=(oo,))
    γ = Symbol(real=True)
    n = Symbol(integer=True)
    Eq << apply(Element(γ, Interval(-1, 0, left_open=True, right_open=True)), Less(Sup[n:oo](Abs(x[n])), oo))

    @Function
    def h(n):
        return (-1) ** n * x[n]
    Eq.h_def = h(n).this.defun()

    Eq << Eq.h_def * (-1) ** n

    Eq << Eq[1].subs(Eq[-1].reversed)

    Eq << sets.el.imply.el.neg.apply(Eq[0])

    Eq << calculus.el_interval.is_finite.imply.is_zero.limit.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].subs(Eq.h_def)

    Eq << Eq[-1].this.find(Mul).args[::2].apply(algebra.mul.to.pow.mul.base)


if __name__ == '__main__':
    run()
# created on 2023-04-18
