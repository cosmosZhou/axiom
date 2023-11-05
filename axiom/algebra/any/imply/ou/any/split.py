from util import *


@apply
def apply(given, *, cond=None, wrt=None):
    from axiom.algebra.all.imply.et.all.split import split
    given = split(Any, given, cond, wrt)
    return given


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    f = Function(integer=True, shape=())
    d = Symbol(real=True, positive=True, given=True)
    Eq << apply(Any[x:Interval(-d, d, left_open=True, right_open=True)](f(x) > 0), cond=x < 0)

    Eq << ~Eq[1]

    Eq << Eq[-1].this.apply(algebra.all.all.imply.all.limits_union)

    
    Eq << ~Eq[-1]
    


if __name__ == '__main__':
    run()
# created on 2023-10-22
