from util import *



@apply
def apply(self):
    p, q = self.of(Imply)
    return Imply(q.invert(), p.invert())


@prove
def prove(Eq):
    from Axiom import Algebra

    p, q = Symbol(bool=True)
    Eq << apply(Imply(p, q))

    Eq << Eq[0].this.lhs.apply(Algebra.Imply.equ.Or)

    Eq << Eq[-1].this.rhs.apply(Algebra.Imply.equ.Or)




if __name__ == '__main__':
    run()

#     https://en.wikipedia.org/wiki/Contraposition
# created on 2018-10-09
# updated on 2022-01-27
