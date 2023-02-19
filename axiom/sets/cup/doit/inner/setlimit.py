from util import *


@apply
def apply(self):
    from axiom.algebra.all.doit.inner.setlimit import doit
    return Equal(self, doit(Cup, self))


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol(etype=dtype.real, shape=(oo, oo))
    i, j, a, b, c, d = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)
    Eq << apply(Cup[j:{a, b, c, d}, i:m](x[i, j]))

    @Function(etype=dtype.real)
    def s(i):
        return Cup[j:{a, b, c, d}](x[i, j])
     
    Eq << s(i).this.defun()

    Eq << sets.eq.imply.eq.cup.apply(Eq[-1], (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(sets.cup.to.union.doit.setlimit)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].reversed

    


if __name__ == '__main__':
    run()

# created on 2021-02-05
# updated on 2022-04-03
