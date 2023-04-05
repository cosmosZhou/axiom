from util import *


@apply
def apply(eq):
    ((r, t), ((s, (S[0], S[t - 1])), S[s[:t - 1].var])), S[r[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced]]])
    t -= 1
    assert s.is_random and r.is_random
    assert t > 0
    return Equal(r[t:] | s[:t], r[t:] | s[t - 1])


@prove
def prove(Eq):
    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) #rewards
    r = Symbol(shape=(oo,), real=True, random=True) #rewards
    t = Symbol(integer=True, positive=True) #time counter
    k = Symbol(integer=True, positive=True, given=False)
    Eq << apply(
        Equal(r[t + 1] | s[:t], r[t + 1])) #conditional independence assumption

    

    


if __name__ == '__main__':
    run()
# created on 2023-04-05
