from util import *


@apply
def apply(gt, prob):
    m, n = gt.of(Greater)
    assert m > 0 and n > 0
    args = prob.of(Probability[Equal])
    if args[-1].is_Tuple:
        (x, x_var), *weights = args
    else:
        x, x_var = args
        weights = []
        
    S[m], *_ = x.shape

    return Equal(Probability(Equal(x, x_var), *weights),
                 Probability(Equal(x[:n], x_var[:n]) & Equal(x[n:m], x_var[n:m]), *weights))

@prove
def prove(Eq):
    from axiom import algebra

    m, n = Symbol(integer=True, positive=True)
    x = Symbol(random=True, real=True, shape=(oo,))
    prob = Probability(x[:m])
    Eq << apply(m > n, prob)

    Eq << algebra.gt.imply.iff.split.eq.apply(Eq[0], *prob.arg.args)

    Eq << Eq[1].subs(Eq[-1])
    Eq << Eq[-1].reversed

    


if __name__ == '__main__':
    run()
# created on 2023-03-26
# updated on 2023-04-05
