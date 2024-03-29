from util import *


@apply
def apply(self, simplify=True):
    from axiom.algebra.sum.to.add import associate
    return associate(All, self, simplify=simplify)


@prove
def prove(Eq):
    from axiom import algebra

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    f, h = Function(real=True)
    Eq << apply(All[i:n]((f(i) > 0) & (h(i) > 0)))

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.all_et.imply.et.all)

    Eq << Eq[-1].this.rhs.apply(algebra.all_et.given.et.all)


if __name__ == '__main__':
    run()

# created on 2018-12-22
