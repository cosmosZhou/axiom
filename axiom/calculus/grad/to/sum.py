from util import *



@apply
def apply(self):
    sgm, *limits_d = self.of(Derivative)
    f, *limits_s = sgm.of(Sum)
    for var, *_ in limits_s:
        for x, n in limits_d:
            if x._has(var):
                break
        else:
            continue
        print(sgm)
        print(self)
        raise "var in summation should not appear in derivative"

    return Equal(self, Sum(Derivative(f, *limits_d).doit(), *limits_s))


@prove
def prove(Eq):
    from axiom import algebra, calculus

    x = Symbol(real=True)
    f = Function(real=True)
    k = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True, given=False)
    Eq << apply(Derivative[x](Sum[k:n](f[k](x))))

    Eq << Eq[0].subs(n, 0)

    Eq << Eq[0].subs(n, n + 1)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.add.pop)

    Eq << Eq[-1].this.lhs.find(Sum).apply(algebra.sum.to.add.pop)

    Eq << Eq[-1].this.lhs.apply(calculus.grad.to.add)

    Eq << Infer(Eq[0], Eq[1], plausible=True)

    Eq << algebra.infer.then.eq.induct.apply(Eq[-1], n)



if __name__ == '__main__':
    run()

# created on 2020-10-17
# updated on 2023-04-07
