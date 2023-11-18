from util import *


# precondition: self.is_Add and factor.is_Add
def try_div_add_args(self_args, factor_args):
    quotient = set()
    for a, b in zip(self_args, factor_args):
        q = try_div(a, b)
        if q is None:
            break

        quotient.add(q)
        if len(quotient) > 1:
            break
    else:
        return quotient.pop()


def try_div(self, factor):
    if self == factor:
        return 1
    if self.is_Mul:
        if factor.is_Mul:
            coeff, [*args] = self.as_coeff_mul()
            _coeff, [*_args] = factor.as_coeff_mul()
            argset = {*args}
            _argset = {*_args}
            if _argset & argset == _argset:
                return Mul(*argset - _argset) * coeff / _coeff
        else:
            for i, arg in enumerate(self.args):
                quotient = try_div(arg, factor)
                if quotient is not None:
                    args = [*self.args]
                    del args[i]
                    return Mul(*args) * quotient
    elif self.is_Add:
        if factor.is_Add:
            if len(self.args) == len(factor.args):
                quotient = try_div_add_args(self.args, factor.args)
#                 if quotient is None:
#                     if len(self.args) == 2:
#                         quotient = try_div_add_args(self.args[::-1], factor.args)
                return quotient

        else:
            args = []
            for i, arg in enumerate(self.args):
                quotient = try_div(arg, factor)
                if quotient is None:
                    return
                args.append(quotient)
            return Add(*args)
    elif self.is_Pow:
        b, e = self.args
        if b == factor:
            if e >= 1:
                return b ** (e - 1)
        elif factor.is_Pow and b == factor.base:
            if (diff := e - factor.exp) >= 0:
                return b ** diff

    elif self.is_Integer:
        if factor.is_Integer:
            if not self % factor:
                return self / factor
    elif self.is_Symbol:
        if factor.is_Mul:
            try:
                index = factor.args.index(self)
                [*args] = factor.args
                del args[index]
                return Mul(*args)
            except IndexError:
                ...


def collect(self, *factors):
    args = self.of(Add)
    additives = []
    others = []
    factor, *factors = factors
    for arg in args:
        quotient = try_div(arg, factor)
        if quotient is None:
            others.append(arg)
        else:
            additives.append(quotient)

    sgm = Add(*additives)
    if factors:
        sgm = collect(sgm, *factors)

    sgm *= factor
    if others:
        sgm += Add(*others)

    return sgm

def search_for_intersection(args):
    from axiom.algebra.add.to.mul import intersect
    for i in range(1, len(args)):
        for j in range(i):
            # j < i             
            ret = intersect(args[i].args if args[i].is_Mul else [args[i]], args[j].args if args[j].is_Mul else [args[j]])
            if ret:
                return i, j, ret

            
@apply(simplify=False)
def apply(self, factor=None):
    args = self.of(Add)
    common_terms = None
    others = []

    additives = []
    if factor is None:
        muls = []
        for arg in args:
            if arg.is_Mul:
                if common_terms is None:
                    common_terms = {*arg.args}
                else:
                    if common_terms & {*arg.args}:
                        common_terms &= {*arg.args}
                    else:
                        others.append(arg)
                        continue
                muls.append(arg)
            else:
                others.append(arg)

        for arg in muls:
            arg = Mul(*{*arg.args} - common_terms)
            additives.append(arg)
            
        if len(additives) > 1:
            factor = Mul(*common_terms)
            additives = Add(*additives)
        else:
            # try a better algorithm to find common terms:
            i, j, common_terms = search_for_intersection(args)
            others = [*args]
            del others[i]
            del others[j]
            
            from axiom.algebra.add.to.mul import factorize
            additives, factor = factorize([args[i], args[j]], common_terms)
        rhs = additives * factor + Add(*others) 
    else:
        if isinstance(factor, (tuple, list)):
            rhs = collect(self, *factor)
        elif factor.is_Mul:
            rhs = collect(self, *factor.args)
        else:
            rhs = collect(self, factor)

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    a, b, x, y = Symbol(complex=True)
    Eq << apply(a * x - a * y + b + b * y, factor=b)

    Eq << Eq[0].this.find(Mul[Add]).apply(algebra.mul.to.add)

    


if __name__ == '__main__':
    run()
# created on 2018-08-02
# updated on 2023-05-20
