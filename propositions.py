class PrimitiveProposition:
    """
    Class to store a primitive proposition like `p` or `q`.
    Just has a name and a string representation equal to the name.
    """

    def __init__(self, name):
        self.name = name

    # String representation is just the name
    def __str__(self):
        return self.name
    
    def __repr__(self):
        return self.name

    # Hashable so can be used in sets
    def __hash__(self):
        return hash(self.name)

    # Equality is based on the name
    def __eq__(self, other):
        return self.__hash__() == other.__hash__()

    # Shorthand hack so (p > q) returns Proposition(p, q)
    def __gt__(self, other):
        return Proposition(self, other)

    # Other bitwise operator overrides
    def __invert__(self):
        return self > false

    def __and__(self, other):
        return ~(self > ~other)

    def __or__(self, other):
        return ~self > other


# Compound propositions are represented as `Proposition` objects in the form `(left => right)`
class Proposition(PrimitiveProposition):
    def __init__(self, left, right):
        self.left = left
        self.right = right
        self.name = f"({self.left} => {self.right})"


# Literal `false` and literal `true` propositions
false = PrimitiveProposition("⊥")
true = ~false

# Some shorthand propositions
p = PrimitiveProposition("p")
q = PrimitiveProposition("q")
r = PrimitiveProposition("r")


class Proof:
    """
    Class to store a proof. Consists of a set of premises and a list of lines, each with an application.
    Provide a set of propositions as premises and then use the methods to add lines to the proof.
    """

    # Constructor: store the premises and initialise the lines and applications
    def __init__(self, premises: set):
        self.premises = premises
        self.lines = list(premises)
        self.applications = ["(premise)" for _ in premises]

    # Apply Axiom 1: `(p => (q => p))`
    def axiom_1(self, p, q):
        self.lines.append(p > (q > p))
        self.applications.append("(A1)")

    # Apply Axiom 2: `(p => (q => r)) => ((p => q) => (p => r))`
    def axiom_2(self, p, q, r):
        self.lines.append((p > (q > r)) > ((p > q) > (p > r)))
        self.applications.append("(A2)")

    # Apply Axiom 3: `~~p => p`
    def axiom_3(self, p):
        self.lines.append(~~p > p)
        self.applications.append("(A3)")

    # Apply Modus Ponens: from `p, (p => q)`, one may deduce `q`
    def modus_ponens(self, p, q):

        # Check that the antecedent and implication are in the proof
        if p not in self.lines:
            raise ValueError(
                f"Antecedent {p} has not been proven: unable to apply modus ponens"
            )

        if (p > q) not in self.lines:
            raise ValueError(
                f"Implication {p > q} has not been proven: unable to apply modus ponens"
            )

        # Add the conclusion to the proof
        self.lines.append(q)
        self.applications.append(
            f"(MP {self.lines.index(p) + 1}, {self.lines.index(p > q) + 1})"
        )

    # Return the last line of the proof as the conclusion
    def conclude(self):
        return self.lines[-1]

    # Print a summary of the proof
    def summary(self):

        # Loop through the lines and applications of the proof and print them out
        for i, (line, application) in enumerate(zip(self.lines, self.applications)):
            print(f"{i+1:>2}. {application:<12} {str(line):<60}")

        # Print the conclusion
        print(
            f"Proved {self.conclude()} from premises {self.premises or '{}'} in {len(self.lines)} lines"
        )
