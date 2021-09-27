from util import *


@apply
def apply(self):
    from axiom.algebra.all.to.et.doit.outer.setlimit import doit
    return Equal(self, doit(Cap, self))


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol(etype=dtype.real, shape=(oo, oo))
    i, j, a, b, c, d = Symbol(integer=True)
    f = Function(integer=True)


    Eq << apply(Cap[j:f(i), i:{a, b, c, d}](x[i, j]))

    Eq << Equal(Cap[j:f(i), i:{a}](x[i, j]), Cap[j:f(a)](x[a, j]), plausible=True)

    Eq << Eq[-1].this.lhs.apply(sets.cap.doit.outer.setlimit)

    Eq << Equal(Cap[j:f(i), i:{b}](x[i, j]), Cap[j:f(b)](x[b, j]), plausible=True)

    Eq << Eq[-1].this.lhs.apply(sets.cap.doit.outer.setlimit)

    Eq << sets.eq.eq.imply.eq.intersect.apply(Eq[-2], Eq[-1])

    Eq << Equal(Cap[j:f(i), i:{c}](x[i, j]), Cap[j:f(c)](x[c, j]), plausible=True)

    Eq << Eq[-1].this.lhs.apply(sets.cap.doit.outer.setlimit)

    Eq << sets.eq.eq.imply.eq.intersect.apply(Eq[-2], Eq[-1])

    Eq << Equal(Cap[j:f(i), i:{d}](x[i, j]), Cap[j:f(d)](x[d, j]), plausible=True)

    Eq << Eq[-1].this.lhs.apply(sets.cap.doit.outer.setlimit)

    Eq << sets.eq.eq.imply.eq.intersect.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

