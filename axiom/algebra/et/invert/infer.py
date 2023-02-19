from util import *


@apply(given=None)
def apply(given, i=-1, j=None):
    [*args] = given.of(And)
    if i < 0:
        i += len(args)
    if j is None:
        j = i - 1

    conj = args[i]
    args[j] = Infer(conj, args[j])
    return Equivalent(given, And(*args), evaluate=False)

@prove
def prove(Eq):
    from axiom import algebra

    a, b, x, y = Symbol(real=True)
    Eq << apply(Greater(x, y) & Greater(a, b))

    Eq << Eq[-1].this.find(Infer).apply(algebra.infer.to.ou)

    Eq << Eq[-1].this.rhs.apply(algebra.et.to.ou)


if __name__ == '__main__':
    run()
# created on 2022-09-20
