from util import *


@apply
def apply(self):
    from axiom.algebra.all.to.et.doit.outer.setlimit import doit
    return Equal(self, doit(Cup, self))


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol(etype=dtype.real, shape=(oo, oo))
    i, j, a, b, c, d = Symbol(integer=True)
    f = Function(integer=True)


    Eq << apply(Cup[j:f(i), i:{a, b, c, d}](x[i, j]))

    Eq << Equal(Cup[j:f(i), i:{a}](x[i, j]), Cup[j:f(a)](x[a, j]), plausible=True)

    Eq << Eq[-1].this.lhs.apply(sets.cup.doit.outer.setlimit)

    Eq << Equal(Cup[j:f(i), i:{b}](x[i, j]), Cup[j:f(b)](x[b, j]), plausible=True)

    Eq << Eq[-1].this.lhs.apply(sets.cup.doit.outer.setlimit)

    Eq << sets.eq.eq.imply.eq.union.apply(Eq[-2], Eq[-1])

    Eq << Equal(Cup[j:f(i), i:{c}](x[i, j]), Cup[j:f(c)](x[c, j]), plausible=True)

    Eq << Eq[-1].this.lhs.apply(sets.cup.doit.outer.setlimit)

    Eq << sets.eq.eq.imply.eq.union.apply(Eq[-2], Eq[-1])

    Eq << Equal(Cup[j:f(i), i:{d}](x[i, j]), Cup[j:f(d)](x[d, j]), plausible=True)

    Eq << Eq[-1].this.lhs.apply(sets.cup.doit.outer.setlimit)

    Eq << sets.eq.eq.imply.eq.union.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-02-08
# updated on 2021-02-08
