from propositions import *
from itertools import product


def use_deduction_theorem(proof, premise):
    """
    Given a proof of some conclusion `q` from a set of premises including `p`,
    we can use the Deduction Theorem (1.13) to show that the set of premises
    without `p` implies `(p => q)`.

    We do this using induction on the lines of the proof: we prove `(p => t)`
    for each line `t` in the proof, and in the case of the final line `q`,
    this gives us `(p => q)` as required.

    For each line, we have four cases to consider:
        - If the line is `p`, then we have `(p => p)` (a provable theorem).
        - If the line is still a premise, then we have `(p => t)` by A1, as
            `t` is a premise.
        - If the line is a statement of an axiom, then we have `(p => t)` by
            A1 again, as `t` is true and thus is implied by any statement.
        - If the line is the result of modus ponens from two previous lines,
            then we have `(p => t)` and `(p => (t => q))` by induction, and
            thus `(p => q)` by A2 and two applications of MP.
    """

    # Make sure that the premise is actually a premise of the proof
    if premise not in proof.premises:
        raise ValueError(f"`{premise}` is not a premise of the proof")

    # Create a new proof with the premise removed
    new_premises = proof.premises - {premise}
    new_proof = Proof(new_premises)

    # Shorthand for the premise
    p = premise

    # Now, loop through the lines of the original proof
    for line, application in zip(proof.lines, proof.applications):

        # Case 1: line is `p` itself: `(p => p)` is a provable theorem
        if line == premise:
            new_proof.axiom_1(p, (p > p))
            new_proof.axiom_2(p, (p > p), p)
            new_proof.modus_ponens(p > ((p > p) > p), (p > (p > p)) > (p > p))
            new_proof.axiom_1(p, p)
            new_proof.modus_ponens(p > (p > p), p > p)

        # Case 2: line is a premise: `(p => t)` by A1
        elif line in proof.premises:
            new_proof.axiom_1(line, p)
            new_proof.modus_ponens(line, p > line)

        # Case 3: line is an axiom: `(p => t)` by A1
        elif application.startswith("(A"):

            # Statement of the axiom
            new_proof.lines.append(line)
            new_proof.applications.append(application)

            # `(p => t)` by A1
            new_proof.axiom_1(line, p)
            new_proof.modus_ponens(line, p > line)

        # Case 4: line is the result of modus ponens
        else:
            for tj, tk in product(proof.lines, repeat=2):
                if tk == (tj > line):
                    break
            else:
                raise ValueError(f"Unable to find the antecedent of {line}")

            # Inductive hypothesis: `(p => tj)` and `(p => (tj => tk))`
            new_proof.axiom_2(p, tj, line)
            new_proof.modus_ponens(p > tk, (p > tj) > (p > line))
            new_proof.modus_ponens(p > tj, p > line)

    return new_proof


# Test the deduction theorem
if __name__ == "__main__":
    proof = Proof({p, q, p > (q > false)})
    proof.modus_ponens(p, q > false)
    proof.modus_ponens(q, false)
    proof.summary()

    new = use_deduction_theorem(proof, p > (q > false))
    new.summary()
