from util import *


@apply
def apply(self):
    t, x = self.of(Expr + Ceiling)
    return Equal(self, Ceiling(x + t), evaluate=False)


@prove
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(Ceiling(x - S.One / 2) + 1)

    x = Symbol(Eq[0].find(Ceiling).arg)
    Eq << x.this.definition

    Eq << Eq[0].subs(Eq[-1].reversed)


if __name__ == '__main__':
    run()
# created on 2018-11-07
