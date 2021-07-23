from util import *


@apply(given=None)
def apply(given, lhs=-1, rhs=None):
    from axiom.algebra.eq.transposition import transposition
    return Equivalent(given, transposition(LessEqual, given, lhs=lhs, rhs=rhs), evaluate=False)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    a = Symbol.a(real=True)
    Eq << apply(LessEqual(x + a, y))

    Eq << Eq[-1].this.rhs + x


if __name__ == '__main__':
    run()