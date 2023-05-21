from util import *


def complement(argset, factor):
    for arg in argset:
        if arg == factor:
            argset.remove(arg)
            return argset

        if arg.is_Pow:
            b, e = arg.args
            if b == factor:
                if e.is_Integer and e > 1:
                    argset.remove(arg)
                    argset.add(b ** (e - 1))
                    return argset
                
                elif e.is_Add:
                    if any(e.is_Integer and e >= 1 for e in e.args):
                        argset.remove(arg)
                        argset.add(b ** (e - 1))
                        return argset
                    
            elif factor.is_Pow and factor.base == b:
                exp = factor.exp
                if e.is_Integer:
                    if e > 0 and exp > 0 and e > exp or e < 0 and exp < 0 and e < exp:
                        argset.remove(arg)
                        argset.add(b ** (e - exp))
                        return argset
                    
        elif arg == -factor:
            argset.remove(arg)
            argset.add(-1)
            return argset

#precondition: if y.is_Pow:
def extract_pow(x, y):
    by, ey = y.args
    if by == x:
        if ey.is_Integer and ey > 1:
            return x
        
        elif ey.is_Add:
            if any(e.is_Integer and e >= 1 for e in ey.args):
                return x
                
    elif x.is_Pow:
        bx, ex = x.args
        if bx == by:
            if ex.is_Add:
                argset = {*ex.args}
                if ey in argset or ey.is_Add and all(e in argset for e in ey.args):
                    return y
                    
            if ex.is_Integer and ey.is_Integer:
                if ex > 0 and ey > 0:
                    return bx ** min(ex, ey)
                
                if ex < 0 and ey < 0:
                    return bx ** max(ex, ey)

    
def intersect(lhs, rhs):
    ret = set()
    for x in lhs:
        for y in rhs:
            if x == y:
                ret.add(x)
                break

            elif y.is_Pow:
                if z := extract_pow(x, y):
                    ret.add(z)
                    break

            elif x == -y:
                if x.is_Mul:
                    if x._coeff_isneg():
                        ret.add(y)
                    else:
                        ret.add(y)
                
                elif x.is_Add and y.is_Add:
                    if x.args[0]._coeff_isneg() and y.args[0]._coeff_isneg():
                        ret.add(y)
                    else:
                        ret.add(x)
                else:
                    ret.add(x)
                break

            elif x.is_Pow:
                if z := extract_pow(y, x):
                    ret.add(z)
                    break

    return ret

def factorize(args, common_terms):
    factor = Mul(*common_terms)
    additives = []
    for arg in args:
        if arg.is_Mul:
            argset = {*arg.args}
            for c in common_terms:
                argset = complement(argset, c)

            additives.append(Mul(*argset))
        elif arg.is_Pow:
            b, e1 = arg.args
            S[b], e0 = factor.of(Pow)
            additives.append(b ** (e1 - e0))
        else:
            assert arg == factor
            additives.append(1)
            
    return Add(*additives), factor

def rewrite(self):
    args = self.of(Add)
    common_terms = None
    for arg in args:
        if arg.is_Mul:
            if common_terms is None:
                common_terms = {*arg.args}
            else:
                common_terms = intersect(common_terms, arg.args)
        else:
            if common_terms is None:
                common_terms = {arg}
            else:
                common_terms = intersect(common_terms, [arg])
        if not common_terms:
            return

    return factorize(args, common_terms)


@apply
def apply(self):
    return Equal(self, Mul(*rewrite(self)))


@prove
def prove(Eq):
    a, x, y = Symbol(complex=True)
    Eq << apply(a * x - a * y)

    Eq << Eq[0].this.rhs.expand()


if __name__ == '__main__':
    run()

from . import st
from . import together
# created on 2018-02-21
# updated on 2023-04-30
