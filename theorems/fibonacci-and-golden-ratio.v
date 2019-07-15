Require Import Arith Omega Reals.

(* The standard recursive definition of the Fibonacci numbers *)

Open Scope nat_scope.

Fixpoint fib n := 
  match n with
    0 => 0
  | (S n) => (* this nested match trick helps coq prove n and m are decreasing [1] *)
      match n with
        0 => 1
      | (S m) => fib n + fib m
      end
  end.

(* F_{n+2} = F_{n+1} + F_n *)
Lemma fib_rec : forall n, fib (S (S n)) = fib n + fib (S n).
induction n.
trivial.
simpl.
omega.
Qed.

Close Scope nat_scope.

(* Closed-form definition of the Fibonacci numbers using the golden ratio (phi) [2] *)

Open Scope R_scope.

Definition phi  := (1 + sqrt 5)/2.
Definition phi' := (1 - sqrt 5)/2.

Definition F n := (phi ^ n - phi' ^ n)/(sqrt 5).

(* Next we prove some handy results about phi and phi' *)

(* This is only used to prove sqrt 5 <> 0 but it's handy to have around i suppose [2] *)
Lemma sqrt_pos_neq_0 : forall n, 0 < n -> sqrt n <> 0.
intros n Hgt.
generalize (Rlt_le 0 n Hgt).
intro Hge.
red.
intro Hs_eq_z.
generalize sqrt_eq_0 n Hge Hs_eq_z.
intro H.
absurd (n = 0).
auto with *.
apply H; assumption.
Qed.

Lemma sqrt5_neq_0 : sqrt 5 <> 0.
apply sqrt_pos_neq_0.
prove_sup0. (* proves 0 < 5 *)
Qed.

(* Split this out to shorten later proofs [3] *)
Lemma pow2_sqrt : forall n, 0 <= n -> sqrt n ^ 2 = n.
intros n Hle.
simpl.
replace (sqrt n * (sqrt n * 1)) with (sqrt n * sqrt n) by field. (* 'by field' means 'do basic algebra please' *)
rewrite sqrt_def by (exact Hle). (* sqrt n * sqrt n -> n *)
reflexivity.
Qed.


(* Now: proofs that phi and phi' are the roots of x^2 = x + 1 (CLRS 3.2-6) *)

Lemma phi_root : phi ^ 2 = phi + 1.
unfold phi.
replace (((1 + sqrt 5) / 2) ^ 2) with ((1 + 2 * sqrt 5 + sqrt 5 ^ 2) / 4) by field.
rewrite pow2_sqrt by (unfold Rle; left; prove_sup0). (* sqrt 5 ^ 2 -> 5; 'by ...' proves 0 <= 5 *)
field.
Qed.

Lemma phi'_root : phi' ^ 2 = phi' + 1.
unfold phi'.
replace (((1 - sqrt 5) / 2) ^ 2) with ((1 - 2 * sqrt 5 + sqrt 5 ^ 2) / 4) by field.
rewrite pow2_sqrt by (unfold Rle; left; prove_sup0).
field.
Qed.

(* Slightly generalize the above results for higher powers *)
Lemma phi_root_n : forall n, (phi ^ S (S n)) = (phi ^ n + phi ^ (S n)).
intro.
replace  (phi ^ S (S n)) with ((phi ^ 2) * (phi ^ n)) by (simpl; field). (* field can't do powers, so simplify those to multiplication first *)
rewrite phi_root.
simpl.
field.
Qed.

Lemma phi'_root_n : forall n, (phi' ^ S (S n)) = (phi' ^ n + phi' ^ (S n)).
intro.
replace  (phi' ^ S (S n)) with ((phi' ^ 2) * (phi' ^ n)) by (simpl; field).
rewrite phi'_root.
simpl.
field.
Qed.

(* The main result! (CLRS 3.2-7) *)

(* If we attempt to prove F n = fib n by induction on n, we run into trouble because the inductive step
   needs access to the /two/ 'rungs' before it. You can't generally do that -- i think it could allow
   you to make use of an unbounded number of previous 'rungs', which could lead to unsoundness. All you
   get is the 'rung' before. That is, to prove F (n + 1) = fib (n + 1), we need to know F n = fib n AND
   F (n - 1) = fib (n - 1), but we only get F n = fib n. :(

   So, instead, here's an odd proof technique that gives us access to more than one 'rung' at a time:
   Prove something stronger: /two steps/ at once, giving us access to the previous two 'rungs' simultaneously!
   It's just like the usual 'climbing a ladder' analogy, but you have three legs instead of two.

   Technically this is stronger, but practically it is not any more difficult to do.
   The inductive step now gives us two hypotheses:
     IHn : F n = fib n
     IHSn : F (n + 1) = fib (n + 1)
   and two goals:
     1: F (n + 1) = fib (n + 1)
     2: F (n + 2) = fib (n + 2)
   The 'extra' goal (goal 1) that this technique adds is exactly one of the induction hypotheses!
   Finally, goal 2 is where the "actual" proof happens: algebra it into F (n + 1) + F n = fib (n + 1) + fib n,
   then use the inductive hypotheses to prove the equality.
*)
(* Note: INR ('inject nat to real') converts natural numbers (the realm of fib) to reals (the realm of F) [4] *)
Lemma F_eq_fib' : forall n, F n = INR (fib n) /\ F (S n) = INR (fib (S n)).
induction n.
+ (* base case: split it up and do the arithmetic *)
  unfold F; unfold phi; unfold phi'.
  split; simpl; field; apply sqrt5_neq_0.
+ (* inductive case *)
  destruct IHn as [IHn IHSn]. (* make that inductive hypothesis more presentable *)
  split. (* split the goal into two, just like solomon would have wanted *)
  exact IHSn. (* goal 1: easy peasy; already done it! *)
  unfold F in *. (* goal 2: actually requires some thinking *)
  rewrite phi_root_n. (* Use phi^2 = phi + 1 to make enough phi terms for F n and F (n + 1) *)
  rewrite phi'_root_n.
  replace ((phi ^ n + phi ^ S n - (phi' ^ n + phi' ^ S n)) / sqrt 5)
    with (((phi ^ n - phi' ^ n) / sqrt 5) + ((phi ^ S n - phi' ^ S n) / sqrt 5))
    by (simpl; field; apply sqrt5_neq_0).
    (* algebra ain't hard when you got a, uh, piece of scratch paper and a computer to check it! *)
  rewrite IHn. (* ahh, the refreshing taste of induction *)
  rewrite IHSn.
  rewrite <- plus_INR. (* INR (fib n) + INR (fib (n + 1)) -> INR (fib n + fib (n + 1)) *)
  rewrite fib_rec. (* fib (n + 2) -> fib n + fib (n + 1) *)
  trivial.
Qed.

(* The actual result we were after follows directly from the more complex result. *)
Lemma F_eq_fib : forall n, F n = INR (fib n).
apply F_eq_fib'.
Qed.

(* and that's all, folks! *)

(* Foontotes:
 [1]: I learned this trick from https://www.irif.fr/~letouzey/hofstadter_g/doc/Fib.html
 [2]: This proof generalized from the proof of sqrt2_neq_0 from the Rtrigo_calc library; see
      https://www.cs.princeton.edu/courses/archive/fall07/cos595/stdlib/html/Coq.Reals.Rtrigo_calc.html#sqrt2_neq_0
 [3]: They give us sqrt_pow2: forall x : R, 0 <= x -> sqrt (x ^ 2) = x but not the other way around!
 [4]: Defined in Raxioms: https://coq.inria.fr/distrib/8.4pl6/stdlib/Coq.Reals.Raxioms.html#INR
      but see Rineq (???) for handy theorems: https://coq.inria.fr/library/Coq.Reals.RIneq.html#lab145
*)

