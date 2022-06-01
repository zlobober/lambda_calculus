import copy
from dataclasses import dataclass

from typing import Optional, Set, Dict


LAMBDA = "λ"


@dataclass
class Var:
    index: int

    def __str__(self):
        return f"z{self.index}"

    def __repr__(self):
        return str(self)

    def __eq__(self, other):
        return self.index == other.index

    def __hash__(self):
        return hash(self.index)


class VarSet:
    var_set: Set[Var]

    def __init__(self, var_set=None):
        if var_set is None:
            var_set = set()
        self.var_set = var_set

    def __repr__(self):
        return str(self.var_set)

    def pick_fresh(self) -> Var:
        result = Var(0)
        while result in self.var_set:
            result.index += 1
        self.var_set.add(result)
        return result

    def update(self, var_set: 'VarSet'):
        self.var_set.update(var_set.var_set)

@dataclass
class Term:
    # Possible values: var, abs, app.
    kind: str
    # For var and abs, name of the variable.
    var: Optional[Var] = None
    # For app, left operand.
    left: Optional['Term'] = None
    # For abs and app, right operand.
    right: Optional['Term'] = None

    @staticmethod
    def new_var(var: Var):
        return Term("var", var=var)

    @staticmethod
    def new_abs(var: Var, right: 'Term'):
        return Term("abs", var=var, right=right)

    @staticmethod
    def new_app(left: 'Term', right: 'Term'):
        return Term("app", left=left, right=right)

    def distinct_names(self) -> bool:
        """
        Returns True iff for any variable v, it appears in at most one abs node.
        """
        bound_vars: Set[Var] = set()

        def traverse(term: Term) -> bool:
            if term.kind == "var":
                return True
            elif term.kind == "abs":
                if term.var in bound_vars:
                    return False
                bound_vars.add(term.var)
                return traverse(term.right)
            elif term.kind == "app":
                return traverse(term.left) and traverse(term.right)

        return traverse(self)

    @staticmethod
    def parse(s: str) -> 'Term':
        def parse_var(pos: int) -> (Var, int):
            assert s[pos] == 'z'
            pos += 1
            index = 0
            while pos != len(s) and s[pos].isdigit():
                index = 10 * index + int(s[pos])
                pos += 1
            var = Var(index)
            return var, pos

        def parse_app(pos: int) -> (Term, int):
            prev_term: Optional[Term] = None
            while pos < len(s) and s[pos] != ')':
                term, pos = parse_term(pos)
                if prev_term is None:
                    prev_term = term
                else:
                    prev_term = Term.new_app(prev_term, term)
            assert prev_term is not None
            return prev_term, pos

        def parse_term(pos: int) -> (Term, int):
            if s[pos] == LAMBDA:
                # abs
                pos += 1
                var, pos = parse_var(pos)
                assert s[pos] == '.'
                pos += 1
                right, pos = parse_app(pos)
                return Term.new_abs(var=var, right=right), pos
            elif s[pos] == '(':
                # recurse
                pos += 1
                result, pos = parse_app(pos)
                assert s[pos] == ')'
                pos += 1
                return result, pos
            elif s[pos] == 'z':
                var, pos = parse_var(pos)
                return Term.new_var(var), pos
            else:
                assert False

        term, pos = parse_app(0)
        assert pos == len(s)
        return term

    def format(self) -> (str, bool):
        """
        Returns string representation of a term and an indication if it contains a lambda adjacent at its end.
        """
        if self.kind == 'var':
            return str(self.var), False
        elif self.kind == 'app':
            left_str, tail_lambda = self.left.format()
            if tail_lambda:
                left_str = '(' + left_str + ')'
            right_str, tail_lambda = self.right.format()
            if self.right.kind == 'app':
                right_str = '(' + right_str + ')'
                tail_lambda = False
            return left_str + right_str, tail_lambda
        elif self.kind == 'abs':
            right_str, _ = self.right.format()
            return LAMBDA + str(self.var) + '.' + right_str, True
        else:
            assert False

    def __repr__(self):
        s, _ = self.format()
        return s

    def all_vars(self) -> VarSet:
        result = VarSet()

        def traverse(term):
            if term.kind == 'var':
                result.var_set.add(term.var)
            elif term.kind == 'app':
                traverse(term.left)
                traverse(term.right)
            elif term.kind == 'abs':
                result.var_set.add(term.var)
                traverse(term.right)

        traverse(self)
        return result

    def free_vars(self) -> VarSet:
        if self.kind == "var":
            return VarSet({self.var})
        elif self.kind == "app":
            result = self.left.free_vars()
            result.update(self.right.free_vars())
            return result
        elif self.kind == "abs":
            result = self.right.free_vars()
            result.var_set.discard(self.var)
            return result
        else:
            assert False

    def clone_fresh(self, prohibited_var_set: VarSet = VarSet()) -> 'Term':
        """
        Clones term so that:
        - each free variable keeps its name
        - each if a bound variable belongs to prohibited_var_set, it is renamed.
        :return:
        """

        taken_var_set = copy.deepcopy(prohibited_var_set)
        taken_var_set.update(self.all_vars())

        mapping: Dict[Var, Var] = dict()

        def traverse(term: Term) -> Term:
            if term.kind == "abs":
                if term.var in prohibited_var_set.var_set:
                    old_image = mapping.get(term.var)
                    new_image = taken_var_set.pick_fresh()
                    mapping[term.var] = new_image
                    result = term.new_abs(var=new_image, right=traverse(term.right))
                    if old_image is None:
                        del mapping[term.var]
                    else:
                        mapping[term.var] = old_image
                    return result
                else:
                    return term.new_abs(var=term.var, right=traverse(term.right))
            elif term.kind == "app":
                return term.new_app(left=traverse(term.left), right=traverse(term.right))
            elif term.kind == "var":
                image = mapping.get(term.var, term.var)
                return term.new_var(var=image)
            else:
                assert False

        return traverse(self)

    def is_redex(self):
        return self.kind == "app" and self.left.kind == "abs"

    def is_normal(self):
        if self.kind == "var":
            return True
        elif self.kind == "app":
            if self.is_redex():
                return False
            return self.left.is_normal() and self.right.is_normal()
        elif self.kind == "abs":
            return self.right.is_normal()
        else:
            assert False


def reduce_redex(root: Term) -> Term:
    assert root.is_redex()

    reduced_var = root.left.var
    used_var_set = root.left.all_vars()

    substituent = root.right
    used_var_set.update(substituent.all_vars())

    where = root.left.right.clone_fresh(prohibited_var_set=substituent.free_vars())

    def traverse(term: Term) -> Term:
        if term.kind == "var":
            if term.var == reduced_var:
                return substituent.clone_fresh(used_var_set)
            else:
                return term
        elif term.kind == "app":
            return Term.new_app(left=traverse(term.left), right=traverse(term.right))
        elif term.kind == "abs":
            if term.var == reduced_var:
                # It is re-bound, so just return term as is.
                return term
            else:
                return Term.new_abs(var=term.var, right=traverse(term.right))
        else:
            assert False

    return traverse(where)


def reduce_normal(term: Term) -> Term:
    def traverse(term) -> (Term, bool):
        if term.is_redex():
            return reduce_redex(term), True
        elif term.kind == 'var':
            return term, False
        elif term.kind == 'app':
            left, reduced = traverse(term.left)
            if reduced:
                return Term.new_app(left=left, right=term.right), True
            right, reduced = traverse(term.right)
            return Term.new_app(left=left, right=right), reduced
        elif term.kind == 'abs':
            right, reduced = traverse(term.right)
            return Term.new_abs(var=term.var, right=right), reduced
        else:
            assert False

    result, reduced = traverse(term)
    assert reduced

    return result


def normalize(term: Term, verbose=True) -> Term:
    if verbose:
        print(term, end='')
    while not term.is_normal():
        term = reduce_normal(term)
        if verbose:
            print(" ->", term, end='')
    if verbose:
        print()
    return term


if __name__ == "__main__":
    t0 = Term.new_abs(Var(0), Term.new_abs(Var(1), Term.new_var(Var(0))))
    t0.distinct_names()

    t1 = Term.parse("λz0.z0")
    print(t1)
    assert t1.distinct_names()

    t2 = Term.parse("λz0.λz1.z0")
    print(t2)
    assert t2.distinct_names()

    t3 = Term.parse("z0z1(z2λz3.z4z5)z6((z7))")
    print(t3)
    assert t3.distinct_names()

    t4 = Term.parse("λz0.((λz1.λz0.z1)z0)")
    print(t4)
    assert not t4.distinct_names()

    t5 = Term.parse("λz0.λz1.(z0z1λz2.z0z1z2z4)z3")
    print(t5)
    print(t5.clone_fresh())
    print(t5.free_vars())
    print(t5.clone_fresh(VarSet({Var(0)})))

    t6 = Term.parse("λz0.z0λz0.z0")
    print(t6)
    print(t6.clone_fresh())
    print(t6.clone_fresh(VarSet({Var(0)})))
    assert t6.is_normal()

    t7 = Term.parse("(λz0.z0)z1")
    print(t7)
    print(t7, '->', reduce_redex(t7))
    assert not t7.is_normal()

    t8 = Term.parse("(λz0.z0z0)(λz0.z0z0)")
    print(t8, "->", reduce_redex(t8))
    print(t8, "->", reduce_normal(t8))
    assert not t8.is_normal()

    t9 = Term.parse("(z0(λz1.z1)z2)")
    assert t9.is_normal()

    t10 = Term.parse("z0((λz1.z1)z2)")
    assert not t10.is_normal()
    print(t10, "->", reduce_normal(t10))

    S = "(λz0.λz1.λz2.z0z2(z1z2))"
    K = "(λz0.λz1.z0)"

    t11 = Term.parse(f"{S}{K}")
    print(t11, "->", reduce_normal(t11))

    normalize(t11, verbose=True)

    t12 = Term.parse(f"({S}{S})({K}({S}{K}{K}))")
    normalize(t12, verbose=True)

    t13 = Term.parse(f"(λz0.z0z0z0){S}")
    normalize(t13, verbose=True)