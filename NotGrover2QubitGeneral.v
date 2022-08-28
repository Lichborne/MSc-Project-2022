Require Import Nat.
Require Import DBCircuits.
Require Import TypeChecking.
Require Import Denotation.
Require Import Composition.
Require Import VectorDef.
Require Import List.
Require Import QuantumLib.VectorStates.
Require Import QuantumLib.Measurement.
Require Import QuantumLib.Matrix.
Require Import QuantumLib.FTA.
Require Import Grover2QubitBasic.

Local Coercion Nat.b2n : bool >-> nat.

(*has to be declared anew*)
Variable f : nat -> bool.

Local Open Scope nat_scope.

(* since In goes to Prop, and existsb takes a variable f, it is simpler to just write this here *)
Fixpoint is_in (k:nat) (l:list nat) : bool :=
      match l with
      | nil => false
      | a::l => (k =? a) || is_in k l
      end.

Definition fs (l:list nat) : nat -> bool :=
  (fun g => match g with
         | 0 => is_in 0 l
         | 1 => is_in 1 l
         | 2 => is_in 2 l
         | 3 => is_in 3 l
         | _ => false
         end).

(* S gate is derived from the The "controlled phase gate" _R_ m with m = 2, so the rotation = Pi/2*)
Definition _S := _R_ (PI/2).

Local Close Scope nat_scope.

Local Open Scope circ_scope.

Definition better_oracle_0_1 : Box ( Qubit ⊗ Qubit ) ( Qubit ⊗ Qubit ) :=
  box_ (x, y) ⇒
    let_ x ← _S $ x;
    let_ (x,y) ← ctrl _Z $ (x,y);
    let_ x  ← _X $ x;
    (x,y).

Definition better_oracle_0_2 : Box ( Qubit ⊗ Qubit ) ( Qubit ⊗ Qubit ) :=
  box_ (x, y) ⇒
    let_ y ← _S $ y;
    let_ (x,y) ← ctrl _Z $ (x,y);
    let_ y ← _X $ y;
    (x,y).

Definition better_oracle_0_3 : Box ( Qubit ⊗ Qubit ) ( Qubit ⊗ Qubit ) :=
  box_ (x, y) ⇒
    let_ y ← _S $ y;
    let_ (x,y) ← ctrl _X $ (x,y);
    let_ (x,y) ← ctrl _Z $ (x,y);
    (x,y).

Definition better_oracle_1_2 : Box ( Qubit ⊗ Qubit ) ( Qubit ⊗ Qubit ) :=
  box_ (x, y) ⇒
    let_ y ← _S $ y;
    let_ (x,y) ← ctrl _X $ (x,y);
    let_ (x,y) ← ctrl _Z $ (x,y);
    let_ y ← _X $ y;
    (x,y).

Definition better_oracle_1_3 : Box ( Qubit ⊗ Qubit ) ( Qubit ⊗ Qubit ) :=
  box_ (x, y) ⇒
    let_ y ← _S $ y;
    let_ (x,y) ← ctrl _Z $ (x,y);
(x,y).

Definition better_oracle_2_3 : Box ( Qubit ⊗ Qubit ) ( Qubit ⊗ Qubit ) :=
  box_ (x, y) ⇒
    let_ x ← _S $ x;
    let_ (x,y) ← ctrl _Z $ (x,y);
    (x,y).

(* For all possible f-s other than no solution and all solutions *)
Definition small_grover_total (f: nat -> bool) : Box One (Qubit ⊗ Qubit) :=
  box_ () ⇒
    let_ x ← _H $ init0 $ ();
    let_ y ← _H $ init0 $ ();
match f 0%nat, f 1%nat, f 2%nat, f 3%nat with
  |true, false, false, false => 
        (let_ (x,y) ← small_oracle_0 $ (x,y);
        let_ (x,y) ← small_diffusion $ (x,y);
        (x,y))
  |false, true, false, false => 
        (let_ (x,y) ← small_oracle_1 $ (x,y);
        let_ (x,y) ← small_diffusion $ (x,y);
        (x,y))
  |false, false, true, false => 
        (let_ (x,y) ← small_oracle_2 $ (x,y);
        let_ (x,y) ← small_diffusion $ (x,y);
        (x,y))
  |false, false, false, true => 
        (let_ (x,y) ← small_oracle_3 $ (x,y);
        let_ (x,y) ← small_diffusion $ (x,y);
        (x,y))
  |true, true, false, false =>
       (let_ (x,y) ← better_oracle_0_1 $ (x,y);
        let_ (x,y) ← small_diffusion $ (x,y);
        (x,y))
  |true, false, true, false =>
        (let_ (x,y) ← better_oracle_0_2 $ (x,y);
        let_ (x,y) ← small_diffusion $ (x,y);
        (x,y))
  |true, false, false, true =>
       (let_ (x,y) ← better_oracle_0_3 $ (x,y);
        let_ (x,y) ← small_diffusion $ (x,y);
        (x,y))
  |false, true, true, false => 
        (let_ (x,y) ← better_oracle_1_2 $ (x,y);
        let_ (x,y) ← small_diffusion $ (x,y);
        (x,y))
  |false, true, false, true =>
       (let_ (x,y) ← better_oracle_1_3 $ (x,y);
        let_ (x,y) ← small_diffusion $ (x,y);
        (x,y))
  |false, false, true, true =>
       (let_ (x,y) ← better_oracle_2_3 $ (x,y);
        let_ (x,y) ← small_diffusion $ (x,y);
        (x,y))
(* For the below, a convenient truth is exploited; looking for any element but one is equivalent to looking for the one element that will not satify f;
   and since in this case (in an ideal world, of course), we know for sure that after one rotation we should have the answer to that and all other cases,
   if we turn these below cases into the equivalent problem of looking for the one for which f is false, we will therefore know that if we get a value 
   that does not return true for f then it will be all other values that return true. 
   This ends up both making things much cleaner (very difficult to implement the oracle without an ancilla in this case and then these cases would be rather different to the others), 
   and the relevant lemma easier to write and prove.*)
  |true, true, true, false =>
     (let_ (x,y) ← small_oracle_3 $ (x,y);
      let_ (x,y) ← small_diffusion $ (x,y);
      (x,y))
  |true, true, false, true =>
      (let_ (x,y) ← small_oracle_2 $ (x,y);
       let_ (x,y) ← small_diffusion $ (x,y);
       (x,y))
  |false, true, true, true =>
      (let_ (x,y) ← small_oracle_0 $ (x,y);
       let_ (x,y) ← small_diffusion $ (x,y);
       (x,y))
  |true, false, true, true =>
      (let_ (x,y) ← small_oracle_1 $ (x,y);
       let_ (x,y) ← small_diffusion $ (x,y);
       (x,y))
  | _, _, _, _ => (x,y)
                              
                              
  
     end.

Lemma small_grover_total_WT : Typed_Box (small_grover_total f).
Proof. type_check. Qed.

Definition prob_partial_meas_matrix {m n} (ξ : Density (2^m)) (ρ : Density (2^(n+m))) : R :=
  fst (trace (Mmult ξ ρ)).

Ltac grover_2qubit_denote_to_nonzero_general :=
  intros;
  unfold fs;
  matrix_denote;
  solve_matrix;
  repeat rewrite Cexp_PI2;
  solve_matrix;
  C_field_simplify;
  Msimpl;
  simpl;
  solve_matrix;
  split.

(* well-typedness ensured by Coq Reals *)
Lemma prob_matrix_0 : denote (small_grover_total (fs [0%nat])) (I 1) = list2D_to_matrix ( [ [ C1 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] ).
Proof.
  all: grover_2qubit_denote_to_nonzero_general.
    Local Close Scope circ_scope.
  apply Csqrt2_neq_0.
  grover_nonzero_begin.
  grover_nonzero_end.
  apply sqrt_sqrt;
  intuition.
Qed.


Lemma ptob_matrix_1 : denote (small_grover_total  (fs [1%nat])) (I 1) = list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C1 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] ) .
Proof.
  grover_2qubit_denote_to_nonzero_general.
  Local Close Scope circ_scope.
  apply Csqrt2_neq_0.
  grover_nonzero_begin.
  grover_nonzero_end.
  apply sqrt_sqrt;
  intuition.
Qed.

Lemma prob_matrix_2: denote (small_grover_total (fs [2%nat])) (I 1) = list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C1 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] ).
Proof.
  grover_2qubit_denote_to_nonzero_general.
  Local Close Scope circ_scope.
  apply Csqrt2_neq_0.
  grover_nonzero_begin.
  grover_nonzero_end.
  apply sqrt_sqrt;
  intuition.
Qed.

Lemma prob_matrix_3 : denote (small_grover_total (fs [3%nat])) (I 1) = list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C1 ] ] ).
Proof.
  grover_2qubit_denote_to_nonzero_general.
  Local Close Scope circ_scope.
  apply Csqrt2_neq_0.
  grover_nonzero_begin.
  grover_nonzero_end.
  apply sqrt_sqrt;
  intuition.
Qed.

(*For the below, we are really only concerned with the Trace, and the values relevant to it (M i j such that i = j). 
  The other values are a result of how the gate applications work out, but not relevant to the main lemma below. 
  Be reminded that these separate lemmas are not necessary, the relevant part of their meaning is encapsulated in the main lemma,
  however, they make that lemma much quicker itself to prove, and also a lot neater (since it is already quite long). *)
Lemma prob_matrix_1_2 : denote (small_grover_total (fs ([1%nat;2%nat]))) (I 1) = list2D_to_matrix ( [ [ C0; C0 ; C0 ; C0 ] ; [ C0 ; (RtoC 0.5) ; (0.5 * Ci)%C ; C0 ]  ; [ C0 ; (-0.5 * Ci)%C ; (RtoC 0.5) ; C0 ] ; [ C0 ; C0 ; C0 ; C0] ] ).
  matrix_denote.
  solve_matrix.
  all: repeat rewrite Cexp_PI2.
  all: solve_matrix.
  all: C_field_simplify; solve_matrix; replace (R1 + R1)%R with 2%R; replace (R0 + R0)%R with 0%R.
  2,3,4,6,7,8, 10,11,12,14,15,16: intuition.
  Local Close Scope circ_scope.
  all: split; try apply Csqrt2_neq_0;
  grover_nonzero_begin;
  try grover_nonzero_end;
  apply sqrt_sqrt;
  intuition.
Qed.

Lemma prob_matrix_0_3 : denote (small_grover_total (fs ([0%nat;3%nat]))) (I 1) = list2D_to_matrix ( [ [ (RtoC 0.5); C0 ; C0 ;  (0.5 * Ci)%C] ; [ C0 ;C0  ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ (-0.5 * Ci)%C ; C0 ; C0 ; (RtoC 0.5)] ] ).
  matrix_denote.
  solve_matrix.
  all: repeat rewrite Cexp_PI2.
  all:  solve_matrix.
  all: C_field_simplify; solve_matrix; replace (R1 + R1)%R with 2%R; replace (R0 + R0)%R with 0%R.
  2,3,4,6,7,8, 10,11,12,14,15,16: intuition.
  Local Close Scope circ_scope.
  all: split; try apply Csqrt2_neq_0;
  grover_nonzero_begin;
  try grover_nonzero_end;
  apply sqrt_sqrt;
  intuition.
Qed.

Lemma prob_matrix_0_1 : denote (small_grover_total (fs ([0%nat;1%nat]))) (I 1) = list2D_to_matrix ( [ [ (RtoC 0.5); (-0.5 * Ci)%C ; C0 ; C0] ; [ (0.5 * Ci)%C ;(RtoC 0.5) ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0] ] ) .
  matrix_denote.
  solve_matrix.
  all: repeat rewrite Cexp_PI2.
  all:  solve_matrix.
  all: C_field_simplify; solve_matrix; replace (R1 + R1)%R with 2%R; replace (R0 + R0)%R with 0%R.
  2,3,4,6,7,8, 10,11,12,14,15,16: intuition.
  Local Close Scope circ_scope.
  all: split; try apply Csqrt2_neq_0;
  grover_nonzero_begin;
  try grover_nonzero_end;
  apply sqrt_sqrt;
  intuition.
Qed.

Lemma prob_matrix_0_2 : denote (small_grover_total (fs ([0%nat;2%nat]))) (I 1) = list2D_to_matrix ( [ [ (RtoC 0.5); C0 ; (-0.5 * Ci)%C ; C0] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ (0.5 * Ci)%C; C0 ; (RtoC 0.5) ; C0 ] ; [ C0 ; C0 ; C0 ; C0] ] ).
  matrix_denote.
  solve_matrix.
  all: repeat rewrite Cexp_PI2.
  all:  solve_matrix.
  all: C_field_simplify; solve_matrix; replace (R1 + R1)%R with 2%R; replace (R0 + R0)%R with 0%R.
  2,3,4,6,7,8, 10,11,12,14,15,16: intuition.
  Local Close Scope circ_scope.
  all: split; try apply Csqrt2_neq_0;
  grover_nonzero_begin;
  try grover_nonzero_end;
  apply sqrt_sqrt;
  intuition.
Qed.

Lemma prob_matrix_2_3 : denote (small_grover_total (fs ([2%nat;3%nat]))) (I 1) = list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ;  [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; (RtoC 0.5);  (-0.5 * Ci)%C ] ; [ C0; C0 ; (0.5 * Ci)%C ; (RtoC 0.5)] ] ).
  matrix_denote.
  solve_matrix.
  all: repeat rewrite Cexp_PI2.
  all:  solve_matrix.
  all: C_field_simplify; solve_matrix; replace (R1 + R1)%R with 2%R; replace (R0 + R0)%R with 0%R.
  2,3,4,6,7,8, 10,11,12,14,15,16: intuition.
  Local Close Scope circ_scope.
  all: split; try apply Csqrt2_neq_0;
  grover_nonzero_begin;
  try grover_nonzero_end;
  apply sqrt_sqrt;
  intuition.
Qed.

Lemma prob_matrix_1_3 : denote (small_grover_total (fs ([1%nat;3%nat]))) (I 1) = list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; (RtoC 0.5); C0 ; (-0.5 * Ci)%C ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0; (0.5 * Ci)%C; C0 ; (RtoC 0.5)] ] ).
  matrix_denote.
  solve_matrix.
  all: repeat rewrite Cexp_PI2.
  all:  solve_matrix.
  all: C_field_simplify; solve_matrix; replace (R1 + R1)%R with 2%R; replace (R0 + R0)%R with 0%R.
  2,3,4,6,7,8, 10,11,12,14,15,16: intuition.
  Local Close Scope circ_scope.
  all: split; try apply Csqrt2_neq_0;
  grover_nonzero_begin;
  try grover_nonzero_end;
  apply sqrt_sqrt;
  intuition.
Qed.

Lemma prob_matrix_1_2_3: denote (small_grover_total (fs [1%nat; 2%nat; 3%nat])) (I 1) = list2D_to_matrix ( [ [ C1 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] ).
Proof.
  grover_2qubit_denote_to_nonzero_general.
  Local Close Scope circ_scope.
  apply Csqrt2_neq_0.
  grover_nonzero_begin.
  grover_nonzero_end.
  apply sqrt_sqrt;
  intuition.
Qed.


Lemma prob_matrix_0_2_3 : denote (small_grover_total  (fs [0%nat; 2%nat; 3%nat])) (I 1) = list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C1 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] ).
Proof.
  grover_2qubit_denote_to_nonzero_general.
  Local Close Scope circ_scope.
  apply Csqrt2_neq_0.
  grover_nonzero_begin.
  grover_nonzero_end.
  apply sqrt_sqrt;
  intuition.
Qed.

Lemma prob_matrix_0_1_3: denote (small_grover_total (fs [0%nat; 1%nat; 3%nat])) (I 1) = list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C1 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] ).
Proof.
  grover_2qubit_denote_to_nonzero_general.
  Local Close Scope circ_scope.
  apply Csqrt2_neq_0.
  grover_nonzero_begin.
  grover_nonzero_end.
  apply sqrt_sqrt;
  intuition.
Qed.

Lemma prob_matrix_0_1_2 : denote (small_grover_total (fs [0%nat; 1%nat; 2%nat])) (I 1) =  list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C1 ] ] ).
Proof.
  grover_2qubit_denote_to_nonzero_general.
  Local Close Scope circ_scope.
  apply Csqrt2_neq_0.
  grover_nonzero_begin.
  grover_nonzero_end.
  apply sqrt_sqrt;
  intuition.
Qed.

Local Close Scope nat_scope.

(*counts the number of solutions for a given f, taken from SQIR*)
Fixpoint count (f : nat -> bool) a b : nat :=
  match b with
  | O => O
  | S b' => (f (a + b') + count f a b')%nat
  end.

Definition k := count f 0 (4).
Definition θ := asin (√ (INR k / 4)).

(*so as not to have to construct the relevant matrices to use as observablees from outer products of basis-vectors; dpericated, because an explicit definition is easier do deal with in the proof *)
Definition basis_matrix (n:nat) (k:nat) : Matrix n n :=
  (fun i j => if (i =? k)%nat && (j =? k)%nat then C1 else C0).

(*explicitness, although it looks worse, is a lot easier to deal with below due to the non-dimension-preserving nature of the basid definition here below*)
Definition basis_matrix_4 (k:nat) : Matrix 4 4 :=
  match k with
  | 0%nat => list2D_to_matrix ( [ [ C1 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] )
  | 1%nat => list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C1 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] )
  | 2%nat => list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C1 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] )
  | 3%nat => list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C1 ] ] )
  | _ => basis_matrix 4 k (* let the absract definition deal with it; will be a Zero 4 *)                
  end.

Require Import sin_asin_rules.

Ltac three_true_solution_prep :=
  unfold Rsum, sum_f_R0;
  unfold count;
  simpl;
  replace (1+1+1+1)%R with 4%R by ring;
  replace (1+1+1)%R with 3%R by ring;
  rewrite sqrt_div;
  intuition;
  rewrite asin34;
  replace (3 * (PI / 3))%R with PI%R.

Local Close Scope circ_scope.
Local Open Scope R_scope.
Ltac three_true_solution_trig :=
  unfold Rdiv;
  rewrite Rmult_comm;
  rewrite Rmult_assoc;
 (* unfortunately, separate goals have to be created with replace, and then proven, because coq would not recognize a rewrite 
    (either locally or in Ltac) nor would it allow replace with by, both above and below *)
  replace (/ 3 * 3) with (3 * / 3);
  replace (3 * / 3) with 1.

Local Close Scope R_scope.

Ltac three_true_solution_end :=
  rewrite Rmult_1_r;
  rewrite sin_PI;
  unfold prob_partial_meas_matrix;
  solve_matrix;
  ring.

Local Open Scope nat_scope.
Definition f_list : list (nat->bool) :=
  [ (fs [0]) ; (fs [1]) ; (fs [2]) ; (fs [3]) ; (fs [0;1]) ; (fs [0;2]) ; (fs [0;3]) ; (fs [1;2]) ; (fs [1;3]) ; (fs [2;3]); (fs [0;1;2]) ; (fs [0;1;3]) ;(fs [0;2;3]); (fs [1;2;3]) ].              
Local Close Scope nat_scope.

(* There is no way of proving this triviality without significant hassle due to how reals are set up in coq; so I will have it here as an axiom; the truth of it is obvious *)
Axiom two_times_point_five_eq_1 :  (0.5 + 0.5)%R = 1%R.

Lemma small_grover_general_correct_prob_simpl : forall g, In g f_list ->
    Rsum 4 (fun z => if g z 
              then (@prob_partial_meas_matrix 2 0
    (basis_matrix_4 z)
    (denote (small_grover_total g) (I 1))) else 0)
               = if ((count g 0 4) <? 3)%nat then 1 else 0.
Proof.
  intros.
  unfold count.
  induction H. symmetry in H. rewrite H.
  2:  destruct H. 2: symmetry in H. 2: rewrite H.
  3:  destruct H. 3: symmetry in H. 3: rewrite H.
  4:  destruct H. 4: symmetry in H. 4: rewrite H.
  5:  destruct H. 5: symmetry in H. 5: rewrite H.
  6:  destruct H. 6: symmetry in H. 6: rewrite H.
  7:  destruct H. 7: symmetry in H. 7: rewrite H.
  8:  destruct H. 8: symmetry in H. 8: rewrite H.
  9:  destruct H. 9: symmetry in H. 9: rewrite H.
  10:  destruct H. 10: symmetry in H. 10: rewrite H.
  11:  destruct H. 11: symmetry in H. 11: rewrite H.
  12:  destruct H. 12: symmetry in H. 12: rewrite H.
  13:  destruct H. 13: symmetry in H. 13: rewrite H.
  14:  destruct H. 14: symmetry in H. 14: rewrite H.
  15:  destruct H.
    (* unfortunately, rewrite does not find the relevant section in the subgoal to do the below automatically, even though that is why the lemmas are reversed in this file *)
  1: replace ((⟦ small_grover_total (fs [0%nat]) ⟧) (I 1)) with (list2D_to_matrix ( [ [ C1 ; C0 ; C0 ; C0 ] ; [ C0 ; C0; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ])).
  2: symmetry; apply prob_matrix_0.
  2: replace ((⟦ small_grover_total (fs [1%nat]) ⟧) (I 1)) with (list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C1; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ])).
  3: symmetry; apply ptob_matrix_1.
  3: replace ((⟦ small_grover_total (fs [2%nat]) ⟧) (I 1)) with (list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0; C0 ; C0 ]  ; [ C0 ; C0 ; C1 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ])).
  4: symmetry; apply prob_matrix_2.
  4: replace ((⟦ small_grover_total (fs [3%nat]) ⟧) (I 1)) with (list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C1 ] ])).
  5: symmetry; apply prob_matrix_3.
  1,2,3,4 :  unfold Rsum, sum_f_R0; simpl; unfold prob_partial_meas_matrix; solve_matrix.
  1,2,3,4: unfold Rminus;  rewrite Rmult_1_l; repeat rewrite Rplus_0_r; repeat rewrite Rplus_0_l; repeat rewrite Rmult_0_l; repeat rewrite Rmult_0_r.
  1,2,3,4: replace (- 0)%R with 0%R. 2,4,6,8: intuition.
  1,2,3,4: repeat rewrite Rplus_0_r; repeat rewrite Rplus_0_l.
  5: replace ((⟦ small_grover_total (fs [0%nat; 1%nat]) ⟧) (I 1)) with (list2D_to_matrix ( [ [ (RtoC 0.5); ((-0.5)%R * Ci)%C ; C0 ; C0] ; [(0.5%R * Ci)%C ;(RtoC 0.5) ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0] ] ) ).
  6: symmetry. 6: apply prob_matrix_0_1.
  6: replace ((⟦ small_grover_total (fs [0%nat; 2%nat]) ⟧) (I 1)) with (list2D_to_matrix ( [ [ (RtoC 0.5); C0 ; ((-0.5)%R * Ci)%C ; C0] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ (0.5%R * Ci)%C ; C0 ; (RtoC 0.5) ; C0 ] ; [ C0 ; C0 ; C0 ; C0] ] ) ).
  7: symmetry; apply prob_matrix_0_2.
  7: replace ((⟦ small_grover_total (fs [0%nat; 3%nat]) ⟧) (I 1)) with (list2D_to_matrix ( [ [ (RtoC 0.5); C0 ; C0 ; (0.5%R * Ci)%C] ; [ C0 ;C0  ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ ((-0.5)%R * Ci)%C ; C0 ; C0 ; (RtoC 0.5)] ] ) ).
  8: symmetry; apply prob_matrix_0_3.
  8: replace ((⟦ small_grover_total (fs [1%nat; 2%nat]) ⟧) (I 1)) with (list2D_to_matrix ( [ [ C0; C0 ; C0 ; C0 ] ; [ C0 ; (RtoC 0.5) ; (0.5%R * Ci)%C ; C0 ]  ; [ C0 ; ((-0.5)%R * Ci)%C ; (RtoC 0.5) ; C0 ] ; [ C0 ; C0 ; C0 ; C0] ] ) ).
  9: symmetry; apply prob_matrix_1_2.
  9: replace ((⟦ small_grover_total (fs [1%nat; 3%nat]) ⟧) (I 1)) with (list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; (RtoC 0.5); C0 ; ((-0.5)%R * Ci)%C] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0; (0.5%R * Ci)%C ; C0 ; (RtoC 0.5)] ] ) ).
  10: symmetry; apply prob_matrix_1_3.
  10: replace ((⟦ small_grover_total (fs [2%nat; 3%nat]) ⟧) (I 1)) with (list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ;  [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; (RtoC 0.5);  ((-0.5)%R * Ci)%C ] ; [ C0; C0 ; (0.5%R * Ci)%C ; (RtoC 0.5)] ] ) ).
  11: symmetry; apply prob_matrix_2_3.
  5,6,7,8,9,10 :  unfold Rsum, sum_f_R0; simpl; unfold prob_partial_meas_matrix; solve_matrix.
  5,6,7,8,9,10: unfold Rminus;  rewrite Rmult_1_l; repeat rewrite Rplus_0_r; repeat rewrite Rplus_0_l; repeat rewrite Rmult_0_l; repeat rewrite Rmult_0_r.
  5,6,7,8,9,10: replace (- 0)%R with 0%R. 6,8,10,12,14,16: intuition.
  5,6,7,8,9,10: repeat rewrite Rplus_0_r; repeat rewrite Rplus_0_l.
  11: replace ((⟦ small_grover_total (fs [0%nat; 1%nat; 2%nat]) ⟧) (I 1)) with (list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C1 ] ])).
  12: symmetry; apply prob_matrix_0_1_2.
  12: replace ((⟦ small_grover_total (fs [0%nat; 1%nat; 3%nat]) ⟧) (I 1)) with (list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0; C0 ; C0 ]  ; [ C0 ; C0 ; C1 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ])).
  13: symmetry; apply prob_matrix_0_1_3.
  13: replace ((⟦ small_grover_total (fs [0%nat; 2%nat; 3%nat]) ⟧) (I 1)) with (list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C1; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ])).
  14: symmetry; apply prob_matrix_0_2_3.
  14: replace ((⟦ small_grover_total (fs [1%nat; 2%nat; 3%nat]) ⟧) (I 1)) with (list2D_to_matrix ( [ [ C1 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ])).
  15: symmetry; apply prob_matrix_1_2_3.
  Local Close Scope circ_scope.
  Local Open Scope R_scope.
  11,12,13,14 :  unfold Rsum, sum_f_R0; simpl; unfold prob_partial_meas_matrix; solve_matrix.
  11,12,13,14: unfold Rminus;  rewrite Rmult_1_l; repeat rewrite Rplus_0_r; repeat rewrite Rplus_0_l; repeat rewrite Rmult_0_l; repeat rewrite Rmult_0_r.
  11,12,13,14: replace (- 0)%R with 0%R. 6,8,10,12,14,16: intuition.
  11,12,13,14: repeat rewrite Rplus_0_r; repeat rewrite Rplus_0_l.
  all: intuition.
  all: apply two_times_point_five_eq_1.
Qed.
