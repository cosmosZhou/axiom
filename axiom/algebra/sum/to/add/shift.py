from util import *


def rewrite(Sum, self):
    expr, *limits, (i, a, b) = self.of(Sum)
    assert a + 1 <= b    
    if limits:
        front = Sum(expr, *limits)
    else:
        front = expr

    front = front._subs(i, a)    
#     b >= a => b + 1 >= a
    return Sum.operator(Sum[i:a + 1:b](expr, *limits), front)

@apply
def apply(self):
    return Equal(self, rewrite(Sum, self), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f, h = Function(real=True)
    Eq << apply(Sum[i:0:n + 1](f(i) + h(i)))

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.split, cond={0})

    


if __name__ == '__main__':
    run()
# created on 2020-03-23
# updated on 2023-04-03
