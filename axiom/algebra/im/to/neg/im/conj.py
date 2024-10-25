from util import *


@apply
def apply(self):
    arg = self.of(Im)
    return Equal(self, -Im(~arg))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(complex=True, shape=(n,))
    Eq << apply(Im(x * y))

    z = Symbol(x * y)
    Eq << z.this.definition

    Eq << algebra.eq.then.eq.conj.apply(Eq[-1])


    Eq << Eq[0].subs(Eq[1].reversed, Eq[2].reversed)


if __name__ == '__main__':
    run()
# created on 2023-06-24
