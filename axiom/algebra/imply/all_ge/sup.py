from util import *


@apply
def apply(self):
    function, *limits = self.of(Sup)
    return All(GreaterEqual(self, function), *limits)


@prove
def prove(Eq):
    from axiom import algebra
    
    x = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    f = Function(real=True)
    Eq << apply(Sup[x:S](f(x)))
    
    y = Symbol(Eq[0].find(Sup))
    Eq << y.this.definition
    
    Eq << algebra.eq_sup.imply.all_ge.apply(Eq[-1])
    
    Eq << Eq[-1].subs(Eq[1])


if __name__ == '__main__':
    run()