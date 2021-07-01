from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(Equal)
    
    return Equal(Limit(lhs, *limits).simplify(), Limit(rhs, *limits).simplify())


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    
    Eq << apply(Equal(f(x) / x, g(x) / x), (x, 0))
    
    Eq << Eq[1].subs(Eq[0])    


if __name__ == '__main__':
    run()
