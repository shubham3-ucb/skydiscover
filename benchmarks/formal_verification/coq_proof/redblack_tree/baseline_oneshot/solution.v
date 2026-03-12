RB (T _ _ _ _ _) _ |- _ => inv H
         end;
  repeat constructor; auto.
```
Wait, `repeat constructor` will apply `RB_leaf`, `RB_r`, `RB_b`, `NearlyRB_r`, `NearlyRB_b`.
But `RB_b` has a color parameter `c`. `constructor` might guess the wrong color?
No, `RB_b` is:
```coq
| RB_b : forall (c : color) (l r : tree V) (k : key) (v : V) (n : nat),
    RB l Black n ->
    RB r Black n ->
    RB (T Black l k v r) c (S n).
```
If the goal is `RB (T Black ...) Black (S n)`, `constructor` will unify `c` with `Black`.
If the goal is `RB (T Black ...) Red (S n)`, `constructor` will unify `c` with `Red`.
So `constructor` is perfectly safe!

Let's trace a case where `solve_ins_RB` might fail.
What if `destruct t eqn:E` destructs a variable that is NOT in the goal but is in the context?
No, `context [match ?t with ...]` only matches subterms of the GOAL.
So it will only destruct terms that are actually being matched on in `balance`.
But wait! `balance` matches on `t1`. `t1` is `ins k v t1`.
So `destruct (ins k v t1)` is done.
Then `balance` matches on the left child of `ins k v t1`.
So `destruct` will destruct the left child.
This is exactly what we want.

Let's test `solve_ins_RB` mentally on `balance Black (T Red (T Red a x b) y c) z d`.
Goal: `RB (T Red (T Black a x b) y (T Black c z d)) Black (S n)`.
`repeat constructor` will apply `RB_r` (since root is Red, goal color is Black).
Then we need `RB (T Black a x b) Red n` and `RB (T Black c z d) Red n`.
`repeat constructor` will apply `RB_b` (since root is Black, goal color is Red).
Then we need `RB a Black (n-1)` and `RB b Black (n-1)`.
These will exactly match the hypotheses from `inv H`!
Because `NearlyRB (T Red (T Red a x b) y c) n` implies `RB (T Red a x b) Black n` and `RB c Black n`.
`RB (T Red a x b) Black n` implies `RB a Red n` and `RB b Red n`.
Wait! `