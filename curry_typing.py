from main import Term, normalize
from dataclasses import dataclass
from typing import Optional, Set, Dict
import copy
from collections import Counter

@dataclass
class Type():
    # Possible values; var, arrow, root
    kind: str
    var: str = None
    left: Optional["Type"] = None
    right: Optional["Type"] = None
    root: bool = False

    def list_vars(self):
        if self.kind == "var" :
            return set((self.var,))
        return self.left.list_vars() | self.right.list_vars()

    @staticmethod
    def arrow(left, right):
        return Type("arrow", None, left, right)

    def substitute(self, var, type):
        if self.kind == "var":
            if self.var == var:
                return type
            else:
                return self
        else:
            return Type.arrow(self.left.substitute(var, type), self.right.substitute(var, type))

    def __str__(self):
        if self.kind == "var":
            return self.var
        else:
            lhs = str(self.left)
            rhs = str(self.right)
            return f"({lhs} -> {rhs})"


class TypeInferrer():
    def generate_type(self):
        self.counter += 1
        return Type("var", "T" + str(self.counter))

    def add_equation(self, lhs, rhs):
        print(f"Added equation: {lhs} = {rhs}")
        self.equations.append([lhs, rhs])

    def build_equations(self, term, expected_type, context=None):
        if context is None:
            context = {}
        context = copy.deepcopy(context)

        if term.kind == "var":
            if term.var not in context:
                context[term.var] = self.generate_type()
            self.add_equation(context[term.var], expected_type)
            return
        elif term.kind == "abs":
            context[term.var] = self.generate_type()
            right_type = self.generate_type()
            self.add_equation(expected_type, Type.arrow(context[term.var], right_type))
            self.build_equations(term.right, right_type, context)
            return
        elif term.kind == "app":
            left_type = self.generate_type()
            right_type = self.generate_type()
            self.add_equation(left_type, Type.arrow(right_type, expected_type))
            self.build_equations(term.left, left_type, context)
            self.build_equations(term.right, right_type, context)

    def normalization_step(self):
        print("Step")
        for lhs, rhs in self.equations:
            print(f"    {lhs} = {rhs}")

        for pair in self.equations:
            if pair[0].kind == "arrow" and pair[1].kind != "arrow":
                print("Swapping", pair[0], pair[1])
                pair[0], pair[1] = pair[1], pair[0]

        for i, (lhs, rhs) in enumerate(self.equations):
            if lhs.kind == "arrow" and rhs.kind == "arrow":
                print(f"Expand {lhs} = {rhs}")
                self.equations[i:i+1] = []
                self.add_equation(lhs.left, rhs.left)
                self.add_equation(lhs.right, rhs.right)
                return True

            if lhs.kind == "var" and rhs.kind == "arrow" and lhs.var in rhs.list_vars():
                print(f"Failed to normalize: expected {lhs} == {rhs}")
                return False

            if lhs.kind == "var" and rhs.kind == "var" and lhs.var == rhs.var:
                print(f"Drop {lhs} = {rhs}")
                self.equations[i:i+1] = []
                return True

        var1 = None
        var2 = None
        index = None
        for i, (lhs, rhs) in enumerate(self.equations):
            if lhs.kind == "var" and rhs.kind == "var" and not (lhs.root | rhs.root):
                var1 = lhs.var
                var2 = rhs.var
                index = i
                break

        if var1 is not None:
            print(f"Identify {var1} and {var2}")
            self.equations[index:index+1] = []
            for pair in self.equations:
                if var1 in pair[0].list_vars():
                    pair[0] = pair[0].substitute(var1, Type("var", var2))
                if var1 in pair[1].list_vars():
                    pair[1] = pair[1].substitute(var1, Type("var", var2))
            return True


        occurences = Counter()
        for lhs, rhs in self.equations:
            if lhs.kind == "var":
                occurences[lhs.var] += 1
        for var, count in occurences.items():
            if count == 1:
                continue
            print(f"Combining equations for {var}")
            indexes = []
            matches = []
            for i, (lhs, rhs) in enumerate(self.equations):
                if lhs.kind == "var" and lhs.var == var:
                    indexes.append(i)
                    matches.append(rhs)
            assert len(indexes) > 1
            for index in indexes[:0:-1]: # all but first in reverse order
                self.equations[index:index+1] = []
            for i in range(len(matches) - 1):
                self.add_equation(matches[i], matches[i+1])

        if any(x > 1 for x in occurences.values()):
            return True

        rhs_var_set = set()
        for lhs, rhs in self.equations:
            rhs_var_set |= rhs.list_vars()
        print(f"Vars in rhs: {rhs_var_set}")

        for i, (lhs, rhs) in enumerate(self.equations):
            if lhs.kind == "var" and lhs.var not in rhs_var_set and not lhs.root:
                print(f"Dropping redundant var {lhs} = {rhs}")
                self.equations[i:i+1] = []
                return True

        var = None
        corresponding_type = None
        index = None
        for i, (lhs, rhs) in enumerate(self.equations):
            if lhs.kind == "var" and lhs.var in rhs_var_set and not lhs.root:
                var = lhs.var
                corresponding_type = rhs
                index = i
                break
        assert var is not None

        print(f"Substituting {var}")

        for pair in self.equations:
            if var in pair[1].list_vars():
                #  assert pair[1].kind == "arrow"
                pair[1] = pair[1].substitute(var, corresponding_type)
        self.equations[index:index+1] = []
        return True


    def solve_equations(self):
        while len(self.equations) > 1:
            if not self.normalization_step():
                return None
        lhs = self.equations[0][0]
        assert lhs.kind == "var"
        assert lhs.var == "q0"
        return self.equations[0][1]

    def infer(self, term):
        assert not term.free_vars().var_set
        self.equations = []
        self.counter = 0
        self.build_equations(term, Type("var", "q0", None, None, True))
        return self.solve_equations()


if __name__ == "__main__":
    inferrer = TypeInferrer()
    t1 = Term.parse("λz0.z0")
    t2 = Term.parse("(λz0.λz1.z1)z0")
    t3 = Term.parse("λz0.λz1.λz2.z0z1z1")
    t4 = Term.parse("(λz0.λz1.z0)z0z0z0")

    #  print(inferrer.infer(t4))
    S = "(λz0.λz1.λz2.z0z2(z1z2))"
    K = "(λz0.λz1.z0)"

    t12 = Term.parse(f"({S}{S})({K}({S}{K}{K}))")
    tmax = Term.parse("λz2.z2λz1.z1λz0.z2λz1.z0")
    print(inferrer.infer(tmax))
