from util import *


@apply
def apply(self):
    [*args] = self.of(And)

    for i, infer in enumerate(args):
        if infer.is_Infer:
            del args[i]
            r = And(*args)
            break
    else:
        return
            
    p, q = infer.args
    return Infer(p | r.invert(), q & r, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    p, q, r = Symbol(bool=True)
    Eq << apply(And(Infer(p, q), r))

    Eq << Eq[0].this.find(Infer).apply(algebra.infer.to.ou)

    Eq << Eq[-1].this.apply(algebra.et.to.ou)

    Eq << Eq[-1].this.apply(algebra.ou.to.infer, 1)

    


if __name__ == '__main__':
    run()
# created on 2023-04-05
