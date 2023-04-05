from util import *


@apply
def apply(self):
    ((γ, k), (r, (S[k], t))), (S[k], S[0], S[oo]) = self.of(Sum[Symbol ** Symbol * Indexed[Symbol, Symbol + Symbol + 1]])
    return Equal(self, self._subs(t, t + 1) * γ + r[t + 1])


@prove
def prove(Eq):
    from axiom import algebra

    r = Symbol(shape=(oo,), real=True, random=True) #rewards
    t, k = Symbol(integer=True) #time counter
    γ = Symbol(domain=Interval(0, 1, left_open=True)) #Discount factor; penalty to uncertainty of future rewards;
    #myopic for γ = 0; and far-sighted for γ = 1
    #discounted future reward;
    Eq << apply(Sum[k:0:oo](γ ** k * r[t + k + 1]))

    Eq << Eq[0].this.lhs.apply(algebra.sum.to.add.shift)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.limits.subs.offset, 1)

    Eq << Eq[-1].this.find(Pow[Add]).apply(algebra.pow.to.mul.split.exponent)

    
    
    #http://incompleteideas.net/book/bookdraft2017nov5.pdf (3.3 Returns and Episodes: Eq. 3.9)
    
    


if __name__ == '__main__':
    run()
# created on 2023-03-27
# updated on 2023-03-29
