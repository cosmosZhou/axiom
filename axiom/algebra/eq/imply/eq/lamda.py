from util import *


@apply
def apply(given, *limits, simplify=True):
    lhs, rhs = given.of(Equal)
    lhs = Lamda(lhs, *limits)
    rhs = Lamda(rhs, *limits)
    if simplify:
        lhs = lhs.simplify()
        rhs = rhs.simplify()
    return Equal(lhs, rhs)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True, given=True)
    i = Symbol(domain=Range(n))
    f, g = Function(integer=True)
    Eq << apply(Equal(f(i), g(i)), (i,))

    Eq << algebra.eq.imply.eq.invoke.apply(Eq[0], Lamda[i], simplify=False)

    
    


if __name__ == '__main__':
    run()

# created on 2018-04-03
# updated on 2021-12-31