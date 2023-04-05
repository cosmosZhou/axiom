from util import *


@apply
def apply(r_expected_def):
    (((r, t), (((a, S[t - 1]), S[a[t - 1].var]), ((s, S[t - 1]), S[s[t - 1].var]))), (S[r[t]],)), r_st_prev = r_expected_def.of(Equal[Expectation[Conditioned[Indexed, Equal[Indexed] & Equal[Indexed]]]])
    assert s.is_random and a.is_random and r.is_random
    return Equal(r_st_prev, Integral[r[t].var](r[t].var * Integral[s[t].var](Probability(s[t] & r[t], given=s[t - 1] & a[t - 1]))))



@prove
def prove(Eq):
    from axiom import stats
    
    b = Symbol(integer=True, positive=True)
    #states / observation of the agent
    s = Symbol(shape=(oo, b), real=True, random=True) 
    #actions to take by the agent
    a = Symbol(shape=(oo,), integer=True, random=True)
    #rewards from the environment
    r = Symbol(shape=(oo,), real=True, random=True)
    #discrete time step 
    t = Symbol(integer=True) 

    r_expected = Function(r'\textbf{r}', shape=(), real=True)
    Eq << apply(Equal(r_expected[t](s[t - 1].var, a[t - 1].var), Expectation[r[t]](r[t] | s[t - 1] & a[t - 1])))
    
    Eq << Integral[s[t].var](Probability(s[t] & r[t], given=s[t - 1] & a[t - 1])).this.apply(stats.integral.to.prob)
    
    Eq << Eq[0].this.rhs.apply(stats.expect.to.integral)
    
    Eq << Eq[-1].subs(Eq[-2].reversed)
    
    #the expected rewards for state–action pairs as a two-argument function r
    #http://incompleteideas.net/book/bookdraft2017nov5.pdf (Eq. 3.5)
    


if __name__ == '__main__':
    run()
# created on 2023-03-27
