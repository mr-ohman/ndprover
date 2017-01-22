# NDProver
NDProver is a propositional logic prover producing natural deduction proofs.

# Example runs

```
$ echo "~p, ~q |- ~(p | q)" | ./ndprover
~p, ~q |- ~(p | q) has proof:
~p ::: Premise
~q ::: Premise
p -> _ ::: ~e ~p
q -> _ ::: ~e ~q
------OPENING-----------------------------
  p | q ::: Assumption
  ------OPENING-----------------------------
    p ::: Assumption
    _ ::: ->e p, p -> _
  ------CLOSING-----------------------------
  ------OPENING-----------------------------
    q ::: Assumption
    _ ::: ->e q, q -> _
  ------CLOSING-----------------------------
  _ ::: |e p | q
------CLOSING-----------------------------
p | q -> _ ::: ->i
~(p | q) ::: ~i p | q -> _
```

```
$ echo "p -> q, q -> p |- p & q" | ./ndprover
p -> q, q -> p |- p & q has counterexample:
p = False
q = False
```
