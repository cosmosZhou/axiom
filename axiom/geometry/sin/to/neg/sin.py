from util import *


@apply
def apply(self):
    from axiom.geometry.sinh.to.neg.sinh import rewrite
    return Equal(self, rewrite(sin, self), evaluate=False)


@prove
def prove(Eq):
    from axiom import geometry

    x, y = Symbol(complex=True)
    Eq << apply(sin(x - y))

    Eq << Eq[0].this.lhs.apply(geometry.sin.to.sub)

    Eq << Eq[-1].this.rhs.find(Sin).apply(geometry.sin.to.sub)

    


if __name__ == '__main__':
    run()
# created on 2023-06-02
# updated on 2023-11-26
