from util import *


@apply
def apply(el, lt, t=None):
    γ, domain = el.of(Element)
    (r, k), (S[k], S[0], S[oo]) = lt.of(Sup[Abs[Indexed]] < Infinity)
    if t is None:
        t = Symbol(integer=True)

    S[0], S[1] = domain.of(Interval)
    assert domain.right_open
    return Less(Abs(Sum[k:0:oo](γ ** k * r[t + k + 1])), oo, evaluate=False)



@prove
def prove(Eq):
    from axiom import algebra, sets, calculus

    r = Symbol(shape=(oo,), extended_real=True) #rewards
    γ = Symbol(real=True) #Discount factor; penalty to uncertainty of future rewards;
    #myopic for γ = 0; and far-sighted for γ = 1
    k, t = Symbol(integer=True)
    Eq << apply(Element(γ, Interval(0, 1, right_open=True)), Less(Sup[k:0:oo](Abs(r[k])), oo, evaluate=False), t)

    

    

    Eq << algebra.imply.all.le_sup.apply(Eq[1].find(Sup))

    Eq << Eq[-1].subs(k, k + t + 1)

    Eq.is_finite = algebra.le.lt.imply.lt.transit.apply(Eq[-1], Eq[1])

    Eq << sets.el_interval.imply.et.apply(Eq[0])

    Eq << algebra.ge.imply.gt.relax.apply(Eq[-2], -1)

    Eq << algebra.lt.gt.imply.lt.abs.apply(Eq[-2], Eq[-1])

    Eq << calculus.lt.is_finite.imply.is_finite.sum.apply(Eq[-1], Eq.is_finite, k)

    #_eval_is_complex should be changed to _eval_is_extended_complex
    
    


if __name__ == '__main__':
    run()
# created on 2023-03-27
# updated on 2023-03-30
