from util import *


@apply
def apply(given, *, cond=None, wrt=None):
    from Axiom.Algebra.And.All.of.All.split import split
    given = split(Any, given, cond, wrt)
    return given


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True)
    f = Function(integer=True, shape=())
    d = Symbol(real=True, positive=True, given=True)
    Eq << apply(Any[x:Interval(-d, d, left_open=True, right_open=True)](f(x) > 0), cond=x < 0)

    Eq << ~Eq[0]

    Eq << Eq[-1].this.apply(Algebra.And.All.of.All.split, cond=x < 0)


    Eq << ~Eq[1]




if __name__ == '__main__':
    run()
# created on 2023-10-22
