from util import *



@apply
def apply(n):
    i = Symbol(integer=True)
    return Equal(factorial(n), Sum[i:n + 1]((-1) ** (n - i) * i ** n * binomial(n, i)))


@prove
def prove(Eq):
    from axiom import discrete

    n = Symbol(integer=True, nonnegative=True)
    Eq << apply(n)

    x = Symbol(real=True)
    Eq << discrete.difference.to.sum.binom.apply(Difference(x ** n, (x, n)))

    Eq << Eq[-1].this.lhs.apply(discrete.difference.to.factorial)

    

    Eq << Eq[-1].subs(x, 0)

    
    


if __name__ == '__main__':
    run()
# created on 2020-10-13
# updated on 2021-12-01