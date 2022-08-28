Require Import Grover2QubitTotal.
Require Import Grover2QubitBasic.
Require Import Nat.
Require Import DBCircuits.
Require Import TypeChecking.
Require Import Denotation.
Require Import Composition.
Require Import VectorDef.
Require Import List.
Require Import sin_asin_rules.
Require Import QuantumLib.VectorStates.
Require Import QuantumLib.Measurement.
Require Import QuantumLib.Matrix.
Require Import QuantumLib.FTA.
Require Import Rtrigo_facts.
Require Import FunctionalExtensionality.
Local Open Scope circ_scope.

Definition equal_superposition : Box One (Qubit ⊗ Qubit) :=
  box_ () ⇒
    let_ x ← _H $ init0 $ ();
    let_ y ← _H $ init0 $ ();
(x,y).

Lemma equal_sup_WT : Typed_Box (equal_superposition).
Proof. type_check. Qed.

Lemma equal_sup_correct : denote equal_superposition (I 1) = list2D_to_matrix ( [ [  (RtoC (1 / 4)) ; (RtoC (1/4)) ;(RtoC ((1/4))) ;  (RtoC (1 / 4)) ] ; [ (RtoC (1/4)) ; (RtoC (1 / 4)) ;  (RtoC (1 / 4)) ; (RtoC (1/4)) ]  ; [ (RtoC (1/4)) ; (RtoC (1 / 4)) ; (RtoC (1 / 4))  ; (RtoC (1/4)) ] ; [  (RtoC (1 / 4)) ; (RtoC (1/4)) ; (RtoC (1/4)) ;  (RtoC (1 / 4)) ] ] ).
Proof. matrix_denote. solve_matrix. Qed.

(*the below could be defined in one function with match, but it makes proofs ever so slightly more inconvenient *)
Fixpoint small_grover_iterate_0 (r:nat) : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  match r with
  | 0 => id_circ
  | S r' => box_ (x,y) ⇒
             (let_ (x,y) ← small_grover_iterate_0 r' $ (x,y);
             let_ (x,y) ← small_oracle_0 $ (x,y);
             let_ (x,y) ← small_diffusion $ (x,y);
             (x,y))
  end.
Lemma small_grover_iterate_0_WT : forall r, Typed_Box (small_grover_iterate_0 r).
Proof. type_check. induction r as [ | [ | r ] ]; type_check. Qed.

Fixpoint small_grover_iterate_1 (r:nat) : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  match r with
  | 0 => id_circ
  | S r' => box_ (x,y) ⇒
             (let_ (x,y) ← small_grover_iterate_1 r' $ (x,y);
              let_ (x,y) ← small_oracle_1 $ (x,y);
              let_ (x,y) ← small_diffusion $ (x,y);
             (x,y))
  end.

Lemma small_grover_iterate_1_WT : forall r, Typed_Box (small_grover_iterate_1 r).
Proof. type_check. induction r as [ | [ | r ] ]; type_check. Qed.

Fixpoint small_grover_iterate_2 (r:nat) : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  match r with
  | 0 => id_circ
  | S r' => box_ (x,y) ⇒
             (let_ (x,y) ← small_grover_iterate_2 r' $ (x,y);
              let_ (x,y) ← small_oracle_2 $ (x,y);
              let_ (x,y) ← small_diffusion $ (x,y);
              (x,y))
  end.

Lemma small_grover_iterate_2_WT : forall r, Typed_Box (small_grover_iterate_2 r).
Proof. type_check. induction r as [ | [ | r ] ]; type_check. Qed.

Fixpoint small_grover_iterate_3 (r:nat) : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  match r with
  | 0 => id_circ
  | S r' => box_ (x,y) ⇒
             (let_ (x,y) ← small_grover_iterate_3 r' $ (x,y);
              let_ (x,y) ← small_oracle_3 $ (x,y);
              let_ (x,y) ← small_diffusion $ (x,y);
              (x,y))
  end.

Lemma small_grover_iterate_3_WT : forall r, Typed_Box (small_grover_iterate_3 r).
Proof. type_check. induction r as [ | [ | r ] ]; type_check. Qed.

Fixpoint small_grover_iterate_0_1 (r:nat) : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  match r with
  | 0 => id_circ
  | S r' => box_ (x,y) ⇒
             (let_ (x,y) ← small_grover_iterate_0_1 r' $ (x,y);
              let_ (x,y) ← small_oracle_0_1 $ (x,y);
              let_ (x,y) ← small_diffusion $ (x,y);
              (x,y))
  end.

Lemma small_grover_iterate_0_1_WT : forall r, Typed_Box (small_grover_iterate_0_1 r).
Proof. type_check. induction r as [ | [ | r ] ]; type_check. Qed.

Fixpoint small_grover_iterate_0_2 (r:nat) : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  match r with
  | 0 => id_circ
  | S r' => box_ (x,y) ⇒
             (let_ (x,y) ← small_grover_iterate_0_2 r' $ (x,y);
              let_ (x,y) ← small_oracle_0_2 $ (x,y);
              let_ (x,y) ← small_diffusion $ (x,y);
              (x,y))
  end.

Lemma small_grover_iterate_0_2_WT : forall r, Typed_Box (small_grover_iterate_0_2 r).
Proof. type_check. induction r as [ | [ | r ] ]; type_check. Qed.

Fixpoint small_grover_iterate_0_3 (r:nat) : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  match r with
  | 0 => id_circ
  | S r' => box_ (x,y) ⇒
             (let_ (x,y) ← small_grover_iterate_0_3 r' $ (x,y);
              let_ (x,y) ← small_oracle_0_3 $ (x,y);
              let_ (x,y) ← small_diffusion $ (x,y);
             (x,y))
  end.

Lemma small_grover_iterate_0_3_WT : forall r, Typed_Box (small_grover_iterate_0_3 r).
Proof. type_check. induction r as [ | [ | r ] ]; type_check. Qed.

Fixpoint small_grover_iterate_1_2 (r:nat) : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  match r with
  | 0 => id_circ
  | S r' => box_ (x,y) ⇒
             (let_ (x,y) ← small_grover_iterate_1_2 r' $ (x,y);
              let_ (x,y) ← small_oracle_1_2 $ (x,y);
              let_ (x,y) ← small_diffusion $ (x,y);
              (x,y))
  end.

Lemma small_grover_iterate_1_2_WT : forall r, Typed_Box (small_grover_iterate_1_2 r).
Proof. type_check. induction r as [ | [ | r ] ]; type_check. Qed.

Fixpoint small_grover_iterate_1_3 (r:nat) : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  match r with
  | 0 => id_circ
  | S r' => box_ (x,y) ⇒
             (let_ (x,y) ← small_grover_iterate_1_3 r' $ (x,y);
              let_ (x,y) ← small_oracle_1_3 $ (x,y);
              let_ (x,y) ← small_diffusion $ (x,y);
              (x,y))
  end.

Lemma small_grover_iterate_1_3_WT : forall r, Typed_Box (small_grover_iterate_1_3 r).
Proof. type_check. induction r as [ | [ | r ] ]; type_check. Qed.

Fixpoint small_grover_iterate_2_3 (r:nat) : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  match r with
  | 0 => id_circ
  | S r' => box_ (x,y) ⇒
             (let_ (x,y) ← small_grover_iterate_2_3 r' $ (x,y);
              let_ (x,y) ← small_oracle_2_3 $ (x,y);
              let_ (x,y) ← small_diffusion $ (x,y);
              (x,y))

  end.

Lemma small_grover_iterate_2_3_WT : forall r, Typed_Box (small_grover_iterate_2_3 r).
Proof. type_check. induction r as [ | [ | r ] ]; type_check. Qed.

Fixpoint small_grover_iterate_0_1_2 (r:nat) : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  match r with
  | 0 => id_circ
  | S r' => box_ (x,y) ⇒
             (let_ (x,y) ← small_grover_iterate_0_1_2 r' $ (x,y);
              let_ (x,y) ← small_oracle_0_1_2 $ (x,y);
              let_ (x,y) ← small_diffusion $ (x,y);
              (x,y))
  end.

Lemma small_grover_iterate_0_1_2_WT : forall r, Typed_Box (small_grover_iterate_0_1_2 r).
Proof. type_check. induction r as [ | [ | r ] ]; type_check. Qed.

Fixpoint small_grover_iterate_0_1_3 (r:nat) : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  match r with
  | 0 => id_circ
  | S r' => box_ (x,y) ⇒
             (let_ (x,y) ← small_grover_iterate_0_1_3 r' $ (x,y);
              let_ (x,y) ← small_oracle_0_1_3 $ (x,y);
              let_ (x,y) ← small_diffusion $ (x,y);
              (x,y))
  end.

Lemma small_grover_iterate_0_1_3_WT : forall r, Typed_Box (small_grover_iterate_0_1_3 r).
Proof. type_check. induction r as [ | [ | r ] ]; type_check. Qed.

Fixpoint small_grover_iterate_0_2_3 (r:nat) : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  match r with
  | 0 => id_circ
  | S r' => box_ (x,y) ⇒
             (let_ (x,y) ← small_grover_iterate_0_2_3 r' $ (x,y);
              let_ (x,y) ← small_oracle_0_2_3 $ (x,y);
              let_ (x,y) ← small_diffusion $ (x,y);
              (x,y))
  end.

Lemma small_grover_iterate_0_2_3_WT : forall r, Typed_Box (small_grover_iterate_0_2_3 r).
Proof. type_check. induction r as [ | [ | r ] ]; type_check. Qed.

Fixpoint small_grover_iterate_1_2_3 (r:nat) : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  match r with
  | 0 => id_circ
  | S r' => box_ (x,y) ⇒
             (let_ (x,y) ← small_grover_iterate_1_2_3 r' $ (x,y);
              let_ (x,y) ← small_oracle_1_2_3 $ (x,y);
              let_ (x,y) ← small_diffusion $ (x,y);
              (x,y))
  end.                         

Lemma small_grover_iterate_1_2_3_WT : forall r, Typed_Box (small_grover_iterate_1_2_3 r).
Proof. type_check. induction r as [ | [ | r ] ]; type_check. Qed.


Local Close Scope nat_scope.

Definition small_grover_general_r_rots (f: nat -> bool) (r:nat) : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  box_ (x,y) ⇒
match f 0%nat, f 1%nat, f 2%nat, f 3%nat with
  |true, false, false, false =>
        (let_ (x,y) ← small_grover_iterate_0 r $ (x,y);
        (x,y))
  |false, true, false, false => 
        (let_ (x,y) ← small_grover_iterate_1 r $ (x,y);
        (x,y))
  |false, false, true, false => 
        (let_ (x,y) ← small_grover_iterate_2 r $ (x,y);
        (x,y))
  |false, false, false, true => 
        (let_ (x,y) ← small_grover_iterate_3 r $ (x,y);
        (x,y))
  |true, true, false, false =>
        (let_ (x,y) ← small_grover_iterate_0_1 r $ (x,y);
        (x,y))
  |true, false, true, false =>
        (let_ (x,y) ← small_grover_iterate_0_2 r $ (x,y);
        (x,y))
  |true, false, false, true =>
        (let_ (x,y) ← small_grover_iterate_0_3 r $ (x,y);
        (x,y))
  |false, true, true, false => 
        (let_ (x,y) ← small_grover_iterate_1_2 r $ (x,y);
        (x,y))
  |false, true, false, true =>
        (let_ (x,y) ← small_grover_iterate_1_3 r $ (x,y);
        (x,y))
  |false, false, true, true =>
        (let_ (x,y) ← small_grover_iterate_2_3 r $ (x,y);
        (x,y))
  |true, true, true, false =>
        (let_ (x,y) ← small_grover_iterate_0_1_2 r $ (x,y);
        (x,y))
  |true, true, false, true =>
        (let_ (x,y) ← small_grover_iterate_0_1_3 r $ (x,y);
        (x,y))
  |true, false, true, true =>
        (let_ (x,y) ← small_grover_iterate_0_2_3 r $ (x,y);
        (x,y))
  |false, true, true, true =>
        (let_ (x,y) ← small_grover_iterate_1_2_3 r $ (x,y);
        (x,y))
  | _, _, _, _ => (x,y)
                              
                              
  
end.
(*
Fixpoint small_grover_iterate (tars:nat) (r:nat) : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  match r with
  | 0 => id_circ
  | S r' => box_ (x,y) ⇒
      match tars with
        | 0 => 
            (let_ (x,y) ← small_oracle_0 $ (x,y);
             let_ (x,y) ← small_diffusion $ (x,y);
             let_ (x,y) ← small_grover_iterate 0 r' $ (x,y);
             (x,y))
        | 1 => 
            (let_ (x,y) ← small_oracle_1 $ (x,y);
             let_ (x,y) ← small_diffusion $ (x,y);
             let_ (x,y) ← small_grover_iterate 1 r' $ (x,y);
             (x,y))
        | 2 => 
            (let_ (x,y) ← small_oracle_2 $ (x,y);
             let_ (x,y) ← small_diffusion $ (x,y);
             let_ (x,y) ← small_grover_iterate 2 r' $ (x,y);
             (x,y))
        | 3 => 
            (let_ (x,y) ← small_oracle_3 $ (x,y);
             let_ (x,y) ← small_diffusion $ (x,y);
             let_ (x,y) ← small_grover_iterate 3 r' $ (x,y);
             (x,y))
        | 10 => 
            (let_ (x,y) ← small_oracle_0_1 $ (x,y);
             let_ (x,y) ← small_diffusion $ (x,y);
             let_ (x,y) ← small_grover_iterate 10 r' $ (x,y);
             (x,y))
        | 20 => 
            (let_ (x,y) ← small_oracle_0_2 $ (x,y);
             let_ (x,y) ← small_diffusion $ (x,y);
             let_ (x,y) ← small_grover_iterate 20 r' $ (x,y);
             (x,y))
        | 30 => 
            (let_ (x,y) ← small_oracle_0_3 $ (x,y);
             let_ (x,y) ← small_diffusion $ (x,y);
             let_ (x,y) ← small_grover_iterate 30 r' $ (x,y);
             (x,y))
        | 12 => 
            (let_ (x,y) ← small_oracle_1_2 $ (x,y);
             let_ (x,y) ← small_diffusion $ (x,y);
             let_ (x,y) ← small_grover_iterate 12 r' $ (x,y);
             (x,y))
        | 13 => 
            (let_ (x,y) ← small_oracle_1_3 $ (x,y);
             let_ (x,y) ← small_diffusion $ (x,y);
             let_ (x,y) ← small_grover_iterate 13 r' $ (x,y);
             (x,y))
        | 23 => 
            (let_ (x,y) ← small_oracle_2_3 $ (x,y);
             let_ (x,y) ← small_diffusion $ (x,y);
             let_ (x,y) ← small_grover_iterate 23 r' $ (x,y);
             (x,y))
        | 210 => 
            (let_ (x,y) ← small_oracle_0_1_2 $ (x,y);
             let_ (x,y) ← small_diffusion $ (x,y);
             let_ (x,y) ← small_grover_iterate 210 r' $ (x,y);
             (x,y))
        | 310 => 
            (let_ (x,y) ← small_oracle_0_1_3 $ (x,y);
             let_ (x,y) ← small_diffusion $ (x,y);
             let_ (x,y) ← small_grover_iterate 310 r' $ (x,y);
             (x,y))
        | 320 => 
            (let_ (x,y) ← small_oracle_0_2_3 $ (x,y);
             let_ (x,y) ← small_diffusion $ (x,y);
             let_ (x,y) ← small_grover_iterate 320 r' $ (x,y);
             (x,y))
        | 123 => 
            (let_ (x,y) ← small_oracle_1_2_3 $ (x,y);
             let_ (x,y) ← small_diffusion $ (x,y);
             let_ (x,y) ← small_grover_iterate 123 r' $ (x,y);
             (x,y))
        | _ =>  (x,y)
      end
   end.
Local Close Scope nat_scope.                          

Definition small_grover_general_r_rots (f: nat -> bool) (r:nat) : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  box_ () ⇒
    let_ x ← _H $ init0 $ ();
    let_ y ← _H $ init0 $ ();
match f 0%nat, f 1%nat, f 2%nat, f 3%nat with
  |true, false, false, false =>
        (let_ (x,y) ← small_grover_iterate 0 r $ (x,y);
        (x,y))
  |false, true, false, false => 
        (let_ (x,y) ← small_grover_iterate 1 r $ (x,y);
        (x,y))
  |false, false, true, false => 
        (let_ (x,y) ← small_grover_iterate 2 r $ (x,y);
        (x,y))
  |false, false, false, true => 
        (let_ (x,y) ← small_grover_iterate 3 r $ (x,y);
        (x,y))
  |true, true, false, false =>
        (let_ (x,y) ← small_grover_iterate 10 r $ (x,y);
        (x,y))
  |true, false, true, false =>
        (let_ (x,y) ← small_grover_iterate 20 r $ (x,y);
        (x,y))
  |true, false, false, true =>
        (let_ (x,y) ← small_grover_iterate 30 r $ (x,y);
        (x,y))
  |false, true, true, false => 
        (let_ (x,y) ← small_grover_iterate 12 r $ (x,y);
        (x,y))
  |false, true, false, true =>
        (let_ (x,y) ← small_grover_iterate 13 r $ (x,y);
        (x,y))
  |false, false, true, true =>
        (let_ (x,y) ← small_grover_iterate 23 r $ (x,y);
        (x,y))
  |true, true, true, false =>
        (let_ (x,y) ← small_grover_iterate 210 r $ (x,y);
        (x,y))
  |true, true, false, true =>
        (let_ (x,y) ← small_grover_iterate 310 r $ (x,y);
        (x,y))
  |true, false, true, true =>
        (let_ (x,y) ← small_grover_iterate 320 r $ (x,y);
        (x,y))
  |false, true, true, true =>
        (let_ (x,y) ← small_grover_iterate 123 r $ (x,y);
        (x,y))
  | _, _, _, _ => (x,y)
                              
                              
  
     end.
*)
(* Since the general form first mathes the function to a circuitry, then calls the relevant circuitry separately,
these lemmas have to be reestablished for this generalized version's first iteration (perhaps the equivalence can instead be proven) 
Lemma small_grover_general_rot_equality : forall g, In g f_list ->
    (denote (small_grover_general_i_rots g 1) (I 1))
               = 
                 (denote (small_grover_total g) (I 1)).
Proof.
  intros.
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
  all: matrix_denote.
  all:admit.
Admitted.
 
  all: solve_matrix.
 Qed.*)

Lemma small_grover_general_rot_equality : forall g, In g f_list ->
    (denote (small_grover_general_r_rots g 1) (denote (equal_superposition) (I 1)))
               = 
                 (denote (small_grover_total g) (I 1)).
Proof.
  intros.
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
  all: matrix_denote.
  (*all: solve_matrix.   This works, but takes a rather long while, and we do not end up using this later, so it is instead admitted.
 Qed.*)
  all:admit.
Admitted. 
  

Ltac trig_periodicity_start r :=
  rewrite asin14;
  replace    (S (S (S (S r))))  with (r +4)%nat by intuition;
  symmetry;
  rewrite mult_plus_distr_l;
  rewrite mult_minus_distr_l;
  rewrite mult_plus_distr_l;
  repeat rewrite plus_INR;
  repeat rewrite minus_INR;
  repeat rewrite mult_INR;
  repeat rewrite plus_INR;
  repeat rewrite mult_INR;
  replace (INR 1) with 1%R by easy;
  replace (INR 2) with 2%R by easy;
  replace (2%R *INR 4)%R with (2 * 4)%R;
  replace (2%R *INR 3)%R with (2 * 3)%R;
  unfold Rminus;
  repeat rewrite Rplus_assoc;
  replace   (8 + (- (6) + 1))%R with 3%R by ring;
  replace ( 8 + 1)%R with 9%R by ring;
  repeat rewrite Rmult_plus_distr_r.

Ltac trig_periodicity_start_from_0 r :=
  rewrite asin14;
  symmetry;
  rewrite mult_plus_distr_l;
  repeat rewrite plus_INR;
  repeat rewrite minus_INR;
  repeat rewrite mult_INR;
  repeat rewrite plus_INR;
  repeat rewrite mult_INR;
  replace (INR 1) with 1%R by easy;
  replace (INR 2) with 2%R by easy;
  replace (2%R *INR 2)%R with (2 * 2)%R;
  replace (2%R *INR 3)%R with (2 * 3)%R;
  unfold Rminus;
  repeat rewrite Rplus_assoc.

Lemma one_true_periodic_from_0 : forall r, (sin (INR (2 * r + 1) * asin (√ (1 / 4))) ^ 2)%R =  (sin ( INR (2 * (S (S (S r))) + 1) * asin (√ (1 / 4))) ^ 2)%R.
  
  intros.
  replace (S (S (S r)))%nat with (r+3)%nat by intuition.
  rewrite sqrt_div.
  trig_periodicity_start_from_0 r.
  5,6: intuition.
  2,3,4: unfold INR; R_field.
   replace (2 * 3 + 1)%R with 7%R by R_field.
   rewrite Rmult_plus_distr_r.
   symmetry.
   rewrite Rmult_plus_distr_r.
   rewrite sin_plus.
   symmetry.
   rewrite sin_plus.
   replace ((7 * (PI / 6)))%R with (PI + (PI / 6))%R by  R_field.
   rewrite cos_pi_plus, sin_pi_plus.
   R_field_simplify.
   repeat rewrite Rmult_1_l.
   replace (cos (PI / 6) * cos (2 * INR r * (PI / 6)))%R with (cos (2 * INR r * (PI / 6))*  cos (PI / 6))%R.
   2: rewrite Rmult_comm; reflexivity.
   R_field_simplify.
   reflexivity.
Qed.

Lemma three_true_periodic_from_0 : forall r, (sin (INR (2 * r + 1) * asin (√ (3 / 4))) ^ 2)%R =  (sin ( INR (2 * (S (S (S r))) + 1) * asin (√ (3/ 4))) ^ 2)%R.
  
  intros.
  replace (S (S (S r)))%nat with (r+3)%nat by intuition.
  rewrite sqrt_div.
  rewrite asin34;
  symmetry;
  rewrite mult_plus_distr_l;
  repeat rewrite plus_INR;
  repeat rewrite minus_INR;
  repeat rewrite mult_INR;
  repeat rewrite plus_INR;
  repeat rewrite mult_INR;
  replace (INR 1) with 1%R by easy;
  replace (INR 2) with 2%R by easy;
  replace (2%R *INR 2)%R with (2 * 2)%R;
  replace (2%R *INR 3)%R with (2 * 3)%R;
  unfold Rminus;
  repeat rewrite Rplus_assoc. 
  5,6: intuition.
  2,3,4: unfold INR; R_field.
   replace (2 * 3 + 1)%R with 7%R by R_field.
   rewrite Rmult_plus_distr_r.
   symmetry.
   rewrite Rmult_plus_distr_r.
   rewrite sin_plus.
   symmetry.
   rewrite sin_plus.
   replace ((7 * (PI / 3)))%R with (PI +( PI + (PI / 3)))%R by  R_field.
   rewrite cos_pi_plus, sin_pi_plus.
   rewrite cos_pi_plus, sin_pi_plus.
   R_field_simplify.
   repeat rewrite Rmult_1_l.
   replace (cos (PI / 3) * cos (2 * INR r * (PI / 3)))%R with (cos (2 * INR r * (PI / 3))*  cos (PI / 3))%R.
   2: rewrite Rmult_comm; reflexivity.
   R_field_simplify.
   reflexivity.
Qed.


Lemma one_true_trig_1  :  (sin (INR (2 * 1 + 1) * asin (√ (1 / 4))) ^ 2)%R = 1.
  rewrite mult_1_r.
  replace (2+1)%nat with 3%nat by easy.
  unfold INR.
  replace (1 + 1 + 1)%R with 3%R by ring.
  rewrite sqrt_div. 2,3 : intuition.
  rewrite asin14.
  replace (3 * (PI / 6))%R with (1 * (PI / 2))%R.
  all: rewrite Rmult_1_l.
  rewrite sin_PI2.
  unfold pow.
  ring.
  R_field_simplify.
  reflexivity.
Qed.

Lemma one_true_trig_2  :  (sin (INR (2 * 2 + 1) * asin (√ (1 / 4))) ^ 2)%R = (1/4)%R.
  replace (2*2+1)%nat with 5%nat by easy.
  unfold INR.
  replace (1 + 1 + 1 + 1 + 1)%R with 5%R by ring.
  rewrite sqrt_div. 2,3 : intuition.
  rewrite asin14.
  replace (5 * (PI / 6))%R with (PI - (PI / 6))%R.
  2: { R_field_simplify. reflexivity. }
  rewrite sin_PI_x.
  rewrite sin_PI6.
  unfold pow.
  R_field_simplify.
  reflexivity.
Qed.

Lemma one_true_trig_3  :  (sin (INR (2 * 3 + 1) * asin (√ (1 / 4))) ^ 2)%R = (1/4)%R.
  replace (2*3+1)%nat with 7%nat by easy.
  unfold INR.
  replace (1 + 1 + 1 + 1 + 1 + 1 + 1)%R with 7%R by ring.
  rewrite sqrt_div. 2,3 : intuition.
  rewrite asin14.
  replace (7 * (PI / 6))%R with ((PI / 6) + PI)%R.
  2: { R_field_simplify. reflexivity. }
  rewrite neg_sin.
  rewrite sin_PI6.
  unfold pow.
  R_field_simplify.
  reflexivity.
Qed.

Lemma one_true_periodic : forall r, (r > 3)%nat -> (sin (INR (2 * r + 1) * asin (√ (1 / 4))) ^ 2)%R =  (sin ( INR (2 * (r-3) + 1) * asin (√ (1 / 4))) ^ 2)%R.
  intros.
  destruct r. inversion H.
  destruct r. inversion H. inversion H1.
  destruct r. inversion H. inversion H1. inversion H3.
  destruct r. inversion H. inversion H1. inversion H3. inversion H5.
  rewrite sqrt_div.
  trig_periodicity_start r.
  9,10 : intuition.
  5: intuition.
  2,3,4,5,6,7: unfold INR; R_field_simplify; reflexivity.
  R_field_simplify.
  replace  (2 * 4 * (PI / 6) + (- (2 * 3) * (PI / 6) + 1 * (PI / 6)))%R with (3 * (PI / 6))%R.
  2: { R_field_simplify. reflexivity. }
  replace (2 * 4 * (PI / 6) + 1 * (PI / 6))%R with (9 * (PI / 6))%R.
  2: { R_field_simplify. reflexivity. }
   replace (sin (2 * INR r * (PI / 6) + 3 * (PI / 6)) ^ 2)%R with   (sin (2 * INR r * (PI / 6) + (PI / 2)) ^ 2)%R.
  2: { unfold Rdiv.
       replace (3 * (PI * / 6))%R with ((PI / 2))%R.
       2: { R_field_simplify. reflexivity. }
       unfold Rdiv. reflexivity.
  }
  replace (9 * (PI / 6))%R  with (PI + PI * / 2)%R.
  2: { symmetry. rewrite <- Rmult_comm. unfold Rdiv. rewrite Rmult_assoc. replace (/ 6 * 9)%R with (1 + 1 / 2)%R.
       2: R_field_simplify; reflexivity.
       rewrite Rmult_plus_distr_l.
       unfold Rdiv.
       repeat rewrite Rmult_1_l.
       repeat rewrite Rmult_1_r.
       reflexivity. }
  symmetry.
  rewrite Rplus_comm.
  rewrite Rplus_assoc.
  rewrite sin_pi_plus.
  rewrite Rplus_comm.
  unfold pow.
  repeat rewrite Rmult_1_r.
  rewrite Rmult_opp_opp.
  unfold Rdiv.
  reflexivity.
Qed.

Lemma two_true_trig_1  :  (sin (INR (2 * 1 + 1) * asin (√ (2 / 4))) ^ 2)%R = (1/2)%R.
   rewrite mult_1_r.
  replace (2+1)%nat with 3%nat by easy.
  unfold INR.
  replace (1 + 1 + 1)%R with 3%R by ring.
  rewrite sqrt_div. 2,3 : intuition.
  rewrite asin24.
  rewrite sin_3PI4.
  unfold pow.
  R_field_simplify.
  reflexivity.
  apply sqrt2_neq_0.
 Qed.

Lemma two_true_trig_2  :  (sin (INR (2 * 2 + 1) * asin (√ (2 / 4))) ^ 2)%R = (1/2)%R.
  replace (2*2+1)%nat with 5%nat by easy.
  unfold INR.
  replace (1 + 1 + 1 +1 +1)%R with 5%R by ring.
  rewrite sqrt_div. 2,3 : intuition.
  rewrite asin24.
  replace (5 * (PI / 4))%R with (PI + (PI / 4))%R.
  2: R_field_simplify; reflexivity.
  rewrite sin_pi_plus.
  rewrite sin_PI4.
  unfold pow.
  R_field_simplify.
  reflexivity.
  apply sqrt2_neq_0.
Qed.

Lemma two_true_trig_3  :  (sin (INR (2 * 3 + 1) * asin (√ (2 / 4))) ^ 2)%R = (1/2)%R.
  replace (2*3+1)%nat with 7%nat by easy.
  unfold INR.
  replace (1 + 1 + 1 +1 +1 +1 +1)%R with 7%R by ring.
  rewrite sqrt_div. 2,3 : intuition.
  rewrite asin24.
  replace (7 * (PI / 4))%R with (PI + (3 * PI / 4))%R.
  2: R_field_simplify; reflexivity.
  rewrite sin_pi_plus.
  unfold pow.
  R_field_simplify.
  unfold Rdiv.
  rewrite Rmult_assoc.
  replace (PI * / 4)%R with (PI / 4)%R by easy.
  rewrite sin_3PI4.
  R_field_simplify.
  reflexivity.
  apply sqrt2_neq_0.
Qed.

Lemma sin_pi_period_zero : forall r:nat,  sin (PI * INR r) = 0.
Proof.
  intros. induction r.
  unfold INR. rewrite Rmult_0_r. apply sin_eq_O_2PI_1.
  intuition. apply Rmult_le_pos. intuition. unfold Rle.
  left. apply PI_RGT_0.
  left. reflexivity.
  replace (S r) with (r+1)%nat. 2:intuition.
  rewrite plus_INR. replace (INR 1) with 1%R by easy.
  rewrite Rmult_plus_distr_l. rewrite Rplus_comm.
  rewrite Rmult_1_r.
  rewrite sin_pi_plus.
  rewrite IHr.
  R_field_simplify.
  reflexivity.
Qed.

Lemma two_true_periodic : forall r, (r > 0)%nat -> (sin (INR (2 * r + 1) * asin (√ (2 / 4))) ^ 2)%R = (sin (INR (2 * (r+1) + 1) * asin (√ (2 / 4))) ^ 2)%R.
  intros. destruct r. inversion H.
  destruct r. rewrite two_true_trig_1.
  symmetry.
  replace (1 + 1)%nat with 2%nat by easy.
  rewrite two_true_trig_2.
  reflexivity.
  rewrite sqrt_div.
  rewrite asin24.
  2,3 : intuition.
  replace (S (S r)) with (r + 2)%nat by intuition.
  repeat rewrite mult_plus_distr_l.
  repeat rewrite plus_INR.
  repeat rewrite mult_INR.
  repeat replace (INR 1) with 1%R by easy.
  repeat replace (INR 2) with 2%R by easy.
  rewrite Rplus_assoc.
  replace (2 * 2 + 1)%R with 5%R. 2 : R_field_simplify; reflexivity.
  repeat rewrite Rplus_assoc.
  replace (2 * 2 + (2 * 1 + 1))%R with 7%R. 2: R_field_simplify; reflexivity.
  rewrite Rmult_comm. symmetry. rewrite Rmult_comm. symmetry.
  rewrite Rmult_plus_distr_l. symmetry. rewrite Rmult_plus_distr_l. symmetry.
  repeat rewrite sin_plus.
  replace (PI / 4 * 7)%R with (PI + (3 * (PI / 4)))%R.
  2: R_field_simplify; reflexivity.
  replace (PI / 4 * 5)%R with (PI + (PI / 4))%R.
  2: R_field_simplify; reflexivity.
  repeat rewrite sin_pi_plus.
  repeat rewrite cos_pi_plus.
  rewrite cos_PI4, sin_PI4, cos_3PI4, sin_3PI4.
  R_field_simplify.
  2: apply sqrt2_neq_0.
  replace (2 * sin (PI / 4 * (2 * INR r)) *
             cos (PI / 4 * (2 * INR r)))%R with (sin (2* PI / 4 * (2 * INR r)))%R.
  2: { unfold Rdiv. rewrite Rmult_assoc.  rewrite Rmult_assoc. symmetry.
       rewrite Rmult_assoc.  rewrite Rmult_assoc.
       rewrite  <- Rmult_assoc.
       symmetry.
       apply sin_2a. }
  replace (2 * PI / 4 * (2 * INR r))%R with (PI * INR r)%R. 2: R_field_simplify; reflexivity.
  replace (PI / 4 * (2 * INR r))%R with  (PI / 2 * INR r)%R. 2: R_field_simplify; reflexivity.
  replace (sin (PI * INR r))%R with 0%R.
  R_field_simplify.
  reflexivity.
  symmetry.
  apply sin_pi_period_zero.
Qed.

Lemma three_true_trig_1  :  (sin (INR (2 * 1 + 1) * asin (√ (3 / 4))) ^ 2)%R = 0.
Proof.
  rewrite mult_1_r.
  replace (2+1)%nat with 3%nat by easy.
  unfold INR.
  replace (1 + 1 + 1)%R with 3%R by ring.
  rewrite sqrt_div. 2,3 : intuition.
  rewrite asin34.
  unfold Rdiv.
  rewrite Rmult_comm.
  replace (PI * / 3 * 3)%R with PI%R. 2: { symmetry. rewrite Rmult_assoc. rewrite Rinv_l. 2: easy. apply Rmult_1_r. }
  rewrite sin_PI.
  unfold pow.
  ring.
Qed.

(*Lemma sin_pi_plus : forall x,
    sin (PI + x) = - sin x.
  *)
Lemma three_true_trig_2 :  (sin (INR (2 * 2 + 1) * asin (√ (3 / 4))) ^ 2)%R = (3/4)%R.
Proof.
  replace (2*2+1)%nat with 5%nat by easy.
  unfold INR.
  replace (1 + 1 + 1 + 1 + 1)%R with 5%R by ring.
  rewrite sqrt_div. 2,3 : intuition.
  rewrite asin34.
  unfold Rdiv.
  replace (5 * (PI * / 3))%R  with (PI + 2 * (PI / 3))%R.
  2: { symmetry. rewrite <- Rmult_comm. replace 5%R with (3 + 2)%R by ring.  rewrite Rmult_plus_distr_l.
       replace (PI * / 3 * 3)%R with PI%R.
       2: { symmetry. rewrite Rmult_assoc. rewrite Rinv_l. 2: easy. apply Rmult_1_r. }
                                         rewrite Rmult_comm. symmetry. unfold Rdiv. reflexivity. }
  rewrite sin_pi_plus.
  rewrite sin_2PI3.
  unfold pow.
  rewrite Rmult_1_r.
  rewrite Rmult_opp_opp.
  unfold Rdiv.
  rewrite <- Rmult_assoc.
  replace (√ 3 * / 2 * √ 3)%R with (√ 3 * √ 3 * / 2)%R. 2: { symmetry; rewrite Rmult_comm. rewrite Rmult_assoc. reflexivity. }
                                                      rewrite sqrt_sqrt. 2: intuition.
  rewrite Rmult_assoc.
  replace  (/ 2 * / 2)%R with  (/ ( 2 * 2))%R.
  2 : apply Rinv_mult_distr. 2,3: easy.
  replace ( 2* 2)%R with 4%R by ring.
  reflexivity.
Qed.

Lemma three_true_trig_3 :  (sin (INR (2 * 3 + 1) * asin (√ (3 / 4))) ^ 2)%R = (3/4)%R.
Proof.
  replace (2*3+1)%nat with 7%nat by easy.
  unfold INR.
  replace (1 + 1 + 1 + 1 + 1 +1 +1)%R with 7%R by ring.
  rewrite sqrt_div. 2,3 : intuition.
  rewrite asin34.
  unfold Rdiv.
  replace (7 * (PI * / 3))%R  with (PI + PI + (PI / 3))%R.
  2: { symmetry. rewrite <- Rmult_comm. replace 7%R with (3 + 4)%R by ring.  rewrite Rmult_plus_distr_l.
       replace (PI * / 3 * 3)%R with PI%R. 2: { symmetry. rewrite Rmult_assoc. rewrite Rinv_l. 2: easy. apply Rmult_1_r. }
                                         replace 4%R with (3 + 1)%R by ring.  rewrite Rmult_plus_distr_l.
       replace (PI * / 3 * 3)%R with PI%R. 2: { symmetry. rewrite Rmult_assoc. rewrite Rinv_l. 2: easy. apply Rmult_1_r. }
                                         rewrite Rmult_1_r.
                                         rewrite Rplus_assoc. symmetry. unfold Rdiv. reflexivity. }
  rewrite Rplus_assoc.
  rewrite sin_pi_plus.
  rewrite sin_pi_plus.
  rewrite sin_PI3.
  rewrite Ropp_involutive.
  unfold pow.
  rewrite Rmult_1_r.
  unfold Rdiv.
  rewrite <- Rmult_assoc.
  replace (√ 3 * / 2 * √ 3)%R with (√ 3 * √ 3 * / 2)%R. 2: { symmetry; rewrite Rmult_comm. rewrite Rmult_assoc. reflexivity. }
                                                      rewrite sqrt_sqrt. 2: intuition.
  rewrite Rmult_assoc.
  replace  (/ 2 * / 2)%R with  (/ ( 2 * 2))%R.
  2 : apply Rinv_mult_distr. 2,3: easy.
  replace ( 2* 2)%R with 4%R by ring.
  reflexivity.
Qed.

Lemma three_true_trig_4 :  (sin (INR (2 * 4 + 1) * asin (√ (3 / 4))) ^ 2)%R = 0%R.
Proof.
  replace (2*4+1)%nat with 9%nat by easy.
  unfold INR.
  replace (1 + 1 + 1 + 1 + 1 +1 +1 +1 +1)%R with 9%R by ring.
  rewrite sqrt_div. 2,3 : intuition.
  rewrite asin34.
  unfold Rdiv.
  replace (9 * (PI * / 3))%R  with (3 * PI)%R.
  2: { symmetry. rewrite <- Rmult_comm. rewrite Rmult_assoc. replace (/ 3 * 9)%R with (3)%R.
       2: { replace 9%R with ( 3 + 3 + 3 )%R by ring.           
            repeat rewrite Rmult_plus_distr_l.
            rewrite Rmult_comm.
            rewrite Rinv_r.
            2: easy.
            ring.
       }
       rewrite Rmult_comm.
       reflexivity.
       }
       rewrite sin_eq_0_1.
  unfold pow.
  ring.
  apply ex_intro with (x:=3%Z).
  reflexivity.
Qed.

Lemma three_true_periodic : forall r, (r > 3)%nat -> (sin (INR (2 * r + 1) * asin (√ (3 / 4))) ^ 2)%R =  (sin ( INR (2 * (r-3) + 1) * asin (√ (3 / 4))) ^ 2)%R.
  intros.
  destruct r.
  inversion H.
  destruct r.
  inversion H.
  inversion H1.
  destruct r.
  inversion H.
  inversion H1.
  inversion H3.
  destruct r.
  inversion H.
  inversion H1.
  inversion H3.
  inversion H5.
  rewrite sqrt_div.
   2,3 : intuition.
   rewrite asin34.
   replace    (S (S (S (S r))))  with (r +4)%nat by intuition.
   symmetry.
   rewrite mult_plus_distr_l.
   rewrite mult_minus_distr_l.
   rewrite mult_plus_distr_l.
   repeat rewrite plus_INR.
   repeat rewrite minus_INR.
   repeat rewrite mult_INR.
   repeat rewrite plus_INR.
   repeat rewrite mult_INR.
   2: { replace (2 * 4)%nat with 8%nat by ring.
        replace (2 * 3)%nat with 6%nat by ring.
        intuition. }
   replace (INR 1) with 1%R by easy.
   replace (INR 2) with 2%R by easy.
   replace (2%R *INR 4)%R with (2 * 4)%R.
   2: { unfold INR. ring. }
   replace (2%R *INR 3)%R with (2 * 3)%R.
   2: { unfold INR. ring. }
   replace (2 * 4)%R with 8%R by ring.
   replace (2 * 3)%R with 6%R by ring.
   unfold Rminus.
   repeat rewrite Rplus_assoc.
   replace   (8 + (- (6) + 1))%R with 3%R by ring.
   replace ( 8 + 1)%R with 9%R by ring.
   repeat rewrite Rmult_plus_distr_r.
   replace (sin (2 * INR r * (PI / 3) + 3 * (PI / 3)) ^ 2)%R with   (sin (2 * INR r * (PI / 3)) ^ 2)%R.
   2: { unfold Rdiv. replace (3 * (PI * / 3))%R with PI%R.
        2:{ rewrite Rmult_comm. symmetry. rewrite Rmult_assoc. rewrite Rinv_l. 2: easy. apply Rmult_1_r. }
        rewrite Rplus_comm.
        rewrite sin_pi_plus.
        unfold pow.
        symmetry.
        repeat rewrite Rmult_1_r.
        rewrite Rmult_opp_opp.
        reflexivity.
}                                       
   unfold Rdiv.
   replace (9 * (PI * / 3))%R  with (3 * PI)%R.
  2: { symmetry. rewrite <- Rmult_comm. rewrite Rmult_assoc. replace (/ 3 * 9)%R with (3)%R.
       2: { replace 9%R with ( 3 + 3 + 3 )%R by ring.           
            repeat rewrite Rmult_plus_distr_l.
            rewrite Rmult_comm.
            rewrite Rinv_r.
            2: easy.
            ring.
       }
       rewrite Rmult_comm.
       reflexivity.
  }
   symmetry.
   rewrite Rplus_comm.
   replace (3 * PI)%R with (PI + PI + PI)%R.
   2: { ring. }
   rewrite Rplus_assoc.
   rewrite Rplus_assoc.
   rewrite sin_pi_plus.
   rewrite sin_pi_plus.
   rewrite Ropp_involutive.
   rewrite sin_pi_plus.
   unfold pow.
   repeat rewrite Rmult_1_r.
   rewrite Rmult_opp_opp.
   reflexivity.
Qed.

(* Example of proof using periodicity for f0, r rotations *)
(* -------------------------------------------------------------------------------------------------------------------*)

Definition id_4 := list2D_to_matrix ( [ [ C1 ; C0 ; C0 ; C0 ] ; [ C0 ; C1 ; C0 ; C0 ]  ; [ C0 ; C0 ; C1 ; C0 ] ; [ C0 ; C0 ; C0 ; C1 ] ] ).

Definition unitary_op_0 := (list2D_to_matrix ( [ [1/2; 1/2 ; 1/2 ; 1/2 ] ; [ -(1/2) ; -(1/2) ; 1/2 ; 1/2]  ; [ -(1/2) ; 1/2 ; -(1/2) ; 1/2 ] ; [ -(1/2) ; (1/2) ; (1/2) ; -(1/2) ] ] )).

(* just to be explicit; this is of course true *) 
Lemma unitary_op_0_correct: unitary_op_0  = Mmult (list2D_to_matrix ( [ [-1/2; 1/2 ; 1/2 ; 1/2 ] ; [ (1/2) ; -(1/2) ; 1/2 ; 1/2]  ; [ (1/2) ; 1/2 ; -(1/2) ; 1/2 ] ; [ (1/2) ; (1/2) ; (1/2) ; -(1/2) ] ] )) (list2D_to_matrix  ( [ [ -C1 ; C0 ; C0 ; C0 ] ; [ C0 ; C1 ; C0 ; C0 ]  ; [ C0 ; C0 ; C1 ; C0 ] ; [ C0 ; C0 ; C0 ; C1 ] ] )). Proof. intros. unfold unitary_op_0. solve_matrix. Qed.                                                                                
Definition unitary_op_0_adj :=  (list2D_to_matrix ( [ [ ((1/2)); (-(1/2)) ; (-(1/2)) ; (-(1/2)) ] ; [ (1/2) ; (-(1/2)) ;(1/2); (1/2)]  ; [ (1/2) ; (1/2) ; (-(1/2)) ; (1/2) ] ; [ (1/2) ; (1/2) ; (1/2) ; (-(1/2)) ] ] )).

Lemma unitary_op_0_adj_eq: adjoint unitary_op_0 = (list2D_to_matrix ( [ [ ((1/2)); (-(1/2)) ; (-(1/2)) ; (-(1/2)) ] ; [ (1/2) ; (-(1/2)) ;(1/2); (1/2)]  ; [ (1/2) ; (1/2) ; (-(1/2)) ; (1/2) ] ; [ (1/2) ; (1/2) ; (1/2) ; (-(1/2)) ] ] )).
Proof. unfold unitary_op_0. solve_matrix. Qed.

Lemma unitary_adj_3_eq : forall (a: Square 4), WF_Matrix a -> a × ( adjoint unitary_op_0)  × (adjoint unitary_op_0)  × (adjoint unitary_op_0)  = -1 .* a.
Proof. intros. rewrite unitary_op_0_adj_eq. solve_matrix. Qed.
       
Definition unitary_op_0_double := (list2D_to_matrix ( [ [ -((1/2)); ((1/2)) ; ((1/2)) ; ((1/2)) ] ; [ -(1/2) ; ((1/2)) ;-(1/2); -(1/2)]  ; [ -(1/2) ; -(1/2) ; ((1/2)) ; -(1/2) ] ; [ -(1/2) ;- (1/2) ; -(1/2) ; ((1/2)) ] ] )).

Fixpoint grover_matrix_op_0 (ρ: Density 4) (r:nat): Density 4 :=
  match r with
    | 0%nat => ρ
    | S r' => super unitary_op_0 (grover_matrix_op_0 ρ r')
  end.

Definition eq_sup_2_q :=  list2D_to_matrix ( [ [(1/4) ; (1/4) ; (1/4) ;  (1/4) ] ; [(1/4) ; (1/4) ; (1/4) ;  (1/4) ] ;[(1/4) ; (1/4) ; (1/4) ;  (1/4) ] ;[(1/4) ; (1/4) ; (1/4) ;  (1/4) ] ] ).

Definition observable_0 := list2D_to_matrix ( [ [ C1 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] ).

Lemma inductive_expr: forall ρ r,  (grover_matrix_op_0 ρ (S r)) = super unitary_op_0 (grover_matrix_op_0 ρ r).
Proof. unfold grover_matrix_op_0. reflexivity. Qed.

Ltac only_left := 
match goal with 
|- _ = ?rhs =>remember rhs
end.

Lemma grover_0_iter_2 : (grover_matrix_op_0 eq_sup_2_q 2) = (list2D_to_matrix [ [C1 / 4; -C1 / 4; -C1 / 4; -C1 / 4]; [-C1 / 4; C1 / 4; C1 / 4; C1 / 4]; [-C1 / 4; C1 / 4; C1 / 4; C1 / 4]; [-C1 / 4; C1 / 4; C1 / 4; C1 / 4] ]).
Proof.
  unfold grover_matrix_op_0, eq_sup_2_q, super.
  rewrite unitary_op_0_adj_eq.
  repeat rewrite <- Mmult_assoc.
  replace ( unitary_op_0 × unitary_op_0) with unitary_op_0_double. 2: unfold unitary_op_0, unitary_op_0_double; solve_matrix.
  unfold unitary_op_0_double.
  solve_matrix.
Qed.

Lemma grover_0_iter_3: (grover_matrix_op_0 eq_sup_2_q 3) = (grover_matrix_op_0 eq_sup_2_q 0).
Proof.
  rewrite inductive_expr.
  rewrite grover_0_iter_2.
  unfold grover_matrix_op_0, eq_sup_2_q.
  unfold super.
  rewrite unitary_op_0_adj_eq.
  unfold unitary_op_0.
  solve_matrix.
Qed.

Lemma grover_0_iter_period_of_3: forall r, (grover_matrix_op_0 eq_sup_2_q (S (S (S r)))) = (grover_matrix_op_0 eq_sup_2_q (r)).
  induction r.
  apply grover_0_iter_3.
  rewrite inductive_expr.
  symmetry.
  rewrite inductive_expr.
  apply (cong_eq (Square 4)  (grover_matrix_op_0 eq_sup_2_q r) (grover_matrix_op_0 eq_sup_2_q (S (S (S r)))) ( super unitary_op_0)).
  symmetry.
  apply IHr.
Qed.

Lemma matrix_form_induction_arg : forall r:nat, 
    (@exp_val_meas_matrix 2 observable_0 (grover_matrix_op_0 (eq_sup_2_q) r) =  ((sin (INR (2 * r + 1) * asin (√ (1 / 4)))) ^ 2)%R -> @exp_val_meas_matrix 2 observable_0 (grover_matrix_op_0 (eq_sup_2_q) (S (S (S r)))) =  ((sin (INR (2 * (S (S (S r))) + 1) * asin (√ (1 / 4)))) ^ 2)%R).
Proof.
  intros.
  rewrite grover_0_iter_period_of_3.
  symmetry.
  rewrite <- one_true_periodic_from_0.
  symmetry.
  apply H.
Qed.

(* For the version form only one onwards for expresivity *)
Lemma matrix_form_induction_arg_Sr : forall r:nat, 
    (@exp_val_meas_matrix 2 observable_0 (grover_matrix_op_0 (eq_sup_2_q) (S r)) =  ((sin (INR (2 * (S r) + 1) * asin (√ (1 / 4)))) ^ 2)%R -> @exp_val_meas_matrix 2 observable_0 (grover_matrix_op_0 (eq_sup_2_q) (S (S (S (S r))))) =  ((sin (INR (2 * (S (S (S (S r)))) + 1) * asin (√ (1 / 4)))) ^ 2)%R).
Proof.
  intros;
  rewrite grover_0_iter_period_of_3;
  symmetry;
  rewrite <- one_true_periodic_from_0;
  symmetry.
  apply H.
Qed.

Local Close Scope circ_scope.
Local Close Scope matrix_scope.
Local Open Scope nat_scope.

Lemma nat_ind_3: forall (Pr: nat -> Prop), (Pr 0%nat) -> (Pr 1%nat) -> (Pr 2%nat) -> (forall (n:nat), Pr n -> Pr (S (S (S n)))) ->
    forall (n:nat), Pr n.
Proof.
  intros Pr Pr0 Pr1 Pr2 H.
  assert (G: forall n, Pr n /\ Pr (S n) /\ Pr (S (S n))).
    induction n as [ | n [ Pn PSn ] ]; auto.
    split. 
    destruct PSn.
    apply H0.
    destruct PSn.
    split.
    apply H1.
    apply H.
    apply Pn.
  apply G.
Qed.

Local Close Scope nat_scope.
Local Open Scope circ_scope.

Lemma matrix_form_grover_0_prop0:  @exp_val_meas_matrix 2 observable_0 (grover_matrix_op_0 (eq_sup_2_q)  0) =  ((sin (INR (2 * 0 + 1) * asin (√ (1 / 4)))) ^ 2)%R.
Proof.
  rewrite sqrt_div. rewrite asin14. rewrite mult_0_r. rewrite plus_0_l. unfold INR. rewrite Rmult_1_l.
  2,3: intuition.
  rewrite sin_PI6.
  unfold exp_val_meas_matrix, observable_0.
  solve_matrix.
  R_field.
Qed.

Lemma matrix_form_grover_0_prop1:  @exp_val_meas_matrix 2 observable_0 (grover_matrix_op_0 (eq_sup_2_q)  1) =  ((sin (INR (2 * 1 + 1) * asin (√ (1 / 4)))) ^ 2)%R.
Proof.
  rewrite one_true_trig_1.
  unfold exp_val_meas_matrix.
  replace (grover_matrix_op_0 eq_sup_2_q 1) with observable_0.
  solve_matrix.
  R_field.
  unfold eq_sup_2_q, grover_matrix_op_0, observable_0.
  solve_matrix.
Qed.

Lemma matrix_form_grover_0_prop2:  @exp_val_meas_matrix 2 observable_0 (grover_matrix_op_0 (eq_sup_2_q)  2) =  ((sin (INR (2 * 2 + 1) * asin (√ (1 / 4)))) ^ 2)%R.
Proof.
  rewrite one_true_trig_2.
  rewrite grover_0_iter_2.
   unfold exp_val_meas_matrix, observable_0.
  solve_matrix.
  R_field.
Qed.

(* additional, for the S r case *)
Lemma matrix_form_grover_0_prop3:  @exp_val_meas_matrix 2 observable_0 (grover_matrix_op_0 (eq_sup_2_q)  3) =  ((sin (INR (2 * 3 + 1) * asin (√ (1 / 4)))) ^ 2)%R.
Proof.
  rewrite one_true_trig_3.
  rewrite grover_0_iter_3.
   unfold exp_val_meas_matrix, observable_0.
  solve_matrix.
  R_field.
Qed.

Lemma matrix_form_induction_grover_0_correct : forall r:nat, @exp_val_meas_matrix 2 observable_0 (grover_matrix_op_0 (eq_sup_2_q)  r) =  ((sin (INR (2 * r + 1) * asin (√ (1 / 4)))) ^ 2)%R.
Proof.
  intros.
  apply (nat_ind_3 (fun r0 => @exp_val_meas_matrix 2 observable_0 (grover_matrix_op_0 (eq_sup_2_q)  r0) =  ((sin (INR (2 *  r0 + 1) * asin (√ (1 / 4)))) ^ 2)%R) matrix_form_grover_0_prop0 matrix_form_grover_0_prop1 matrix_form_grover_0_prop2 matrix_form_induction_arg).
Qed.

Lemma matrix_form_induction_grover_0_correct_Sr : forall r:nat, (r > 2)%nat -> @exp_val_meas_matrix 2 observable_0 (grover_matrix_op_0 (eq_sup_2_q)  (S r)) =  ((sin (INR (2 * (S r) + 1) * asin (√ (1 / 4)))) ^ 2)%R.
Proof.
  intros.
  induction r.
  inversion H.
  induction r.
  inversion H. inversion H1.
  induction r.
  inversion H. inversion H1. inversion H3.
  apply (nat_ind_3 (fun r0 => @exp_val_meas_matrix 2 observable_0 (grover_matrix_op_0 (eq_sup_2_q)  (S r0)) =  ((sin (INR (2 * (S r0) + 1) * asin (√ (1 / 4)))) ^ 2)%R) matrix_form_grover_0_prop1 matrix_form_grover_0_prop2 matrix_form_grover_0_prop3 matrix_form_induction_arg_Sr).
Qed.


(* Proof of denotational equivalence using the assumption of denotational composition *)
(*-------------------------------------------------------------------------------------*)


Lemma grover_0_comp: forall (r:nat), 
      denote_box true (small_grover_iterate_0 (S r)) = denote_box true (small_grover_iterate_0 (r);;(small_grover_iterate_0 (1))).
Proof.
  intros.
  unfold inSeq.
  unfold small_grover_iterate_0.
  unfold unbox.
  autounfold with den_db.
  simpl. reflexivity.
Qed.


(*Proof of the inductive construction of circuits *)
Lemma denote_inductive: forall{W} (f: nat -> Box W W) (r:nat), denote_box true (f (S r)) = denote_box true ((f r);;(f 1%nat)) ->
      (forall k:nat, f (S k) = f k ;; f 1%nat) -> denote_box true (f (S (S r))) = denote_box true ((f (S r));;(f 1%nat)).
Proof. intros. rewrite H0. reflexivity. Qed.


Lemma equiv_transf: forall (A:Type) (f: A -> A) (g: A ->A) (a:A) (b:A), a = b -> (f = g -> f a = g b).
  Proof. intros. rewrite H0. apply cong_eq. apply H. Qed.

 Lemma matrix_equiv_1 : forall (ρ:Density 4), WF_Matrix ρ -> denote_box true (small_grover_iterate_0 1) ρ = super unitary_op_0 ρ.
 Proof.
  matrix_denote.
  (* again, solve matrix takes too long, but can solve this goal; simplifications make it so solve_matrix does not run, or else coq does not recognize them; 
  many ways have beenb tried. Regardless, this is solved *)
  (* solve_matrix. R_field.*)
  admit.
  Admitted.
  
Lemma denotation_matrix_equivalencce_grover_0: forall (r:nat) (ρ:Density 4),  WF_Matrix ρ ->
       denote_box true (small_grover_iterate_0  r) ρ = (grover_matrix_op_0 ρ  r).
Proof.
  intros.
  induction r.
  unfold grover_matrix_op_0.
  matrix_denote. solve_matrix.
  rewrite grover_0_comp.
  rewrite inSeq_correct. 2,3: apply small_grover_iterate_0_WT.
  rewrite inductive_expr.
  unfold compose_super.
  symmetry in IHr.
  rewrite IHr.
  apply matrix_equiv_1.
  apply (WF_denote_box true (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) (small_grover_iterate_0 r) ρ).
  apply small_grover_iterate_0_WT.
  apply H.
Qed.

Lemma circ_induction_grover_0_correct : forall (r:nat), @exp_val_meas_matrix 2 observable_0
  (denote_box true (small_grover_iterate_0  r) (denote equal_superposition (I 1))) =
  ((sin (INR (2 * r + 1) * asin (√ (1 / 4)))) ^ 2)%R.
Proof.
  intros.
  replace  (denote equal_superposition (I 1)) with eq_sup_2_q.
  2: matrix_denote; Msimpl; unfold eq_sup_2_q. 2: solve_matrix.
  rewrite denotation_matrix_equivalencce_grover_0.
  2: { unfold eq_sup_2_q. unfold WF_Matrix. intros. rewrite WF_list2D_to_matrix.
       reflexivity. intuition. intros. destruct H0. symmetry in H0. rewrite H0.
       intuition. inversion H0. symmetry in H1. rewrite H1. reflexivity. inversion H1.
       symmetry in H2. 1: rewrite H2. symmetry in H2. reflexivity. inversion H2.
       symmetry in H3. 1: rewrite H3. symmetry in H3. reflexivity. inversion H3.
       intuition. } 
  apply matrix_form_induction_grover_0_correct.
Qed.                                                   
                                                                                              
                                                                                      

 

  (* -------------------------------------------------------------------------------------------------------------------*)
(* this works, but was only an exetrcise in provability. It was a pain; we are not mean to oeprate witch such large expressions   
Lemma period_of_6: forall r, (grover_matrix_op_0 eq_sup_2_q (S (S (S (S (S (S r))))))) = (grover_matrix_op_0 eq_sup_2_q (r)).
  induction r.
  
  unfold grover_matrix_op_0, super.
  repeat rewrite <- Mmult_assoc.
  replace ( unitary_op_0 × unitary_op_0 × unitary_op_0 × unitary_op_0 × unitary_op_0 × unitary_op_0) with id_4.
  2: { replace (unitary_op_0 × unitary_op_0  × unitary_op_0) with (-1 .* id_4). 2: { unfold id_4. solve_matrix.}
                                                                              unfold unitary_op_0, id_4. solve_matrix.}
  symmetry. only_left. replace ((eq_sup_2_q)) with  (id_4 × eq_sup_2_q). 2: { unfold eq_sup_2_q, id_4. solve_matrix. }
                                                                       replace (id_4 × eq_sup_2_q)  with (-1 .* id_4 × eq_sup_2_q × (unitary_op_0) † × (unitary_op_0) † × (unitary_op_0) †).
  2: rewrite unitary_adj_3_eq. 2: unfold eq_sup_2_q; solve_matrix.
  replace (-1 .* id_4 × eq_sup_2_q × (unitary_op_0) † × (unitary_op_0) † × (unitary_op_0) †)  with ( id_4 × eq_sup_2_q × (unitary_op_0) † × (unitary_op_0) † × (unitary_op_0) † × (unitary_op_0) † × (unitary_op_0) † × (unitary_op_0) †).
  2: rewrite unitary_adj_3_eq. 2: rewrite unitary_adj_3_eq. 2: rewrite unitary_adj_3_eq. 2: unfold id_4, eq_sup_2_q; solve_matrix.
  4: rewrite unitary_adj_3_eq; solve_matrix.
  rewrite Heqm.
  reflexivity.
  2,3,4: replace id_4 with (I 4); try unfold id_4. 3,5,7: solve_matrix.
  1,2,3,4,5: unfold eq_sup_2_q, unitary_op_0, id_4.
  all: try rewrite Mmult_1_l.
  (* unfortunately there is no way to rewrite using matrix solution only replace *)
  (* also, rplace statements once again did not work with some matrices unless unfolded *)
  1, 8:replace (-1 .* list2D_to_matrix [ [C1; C0; C0; C0]; [C0; C1;C0; C0]; [C0; C0; C1; C0]; [C0; C0; C0; C1] ]
     × list2D_to_matrix
         [ [C1 / 4; C1 / 4; C1 / 4; C1 / 4]; [C1 / 4; C1 / 4; C1 / 4; C1 / 4]; [C1 / 4; C1 / 4; C1 / 4; C1 / 4];
         [C1 / 4; C1 / 4; C1 / 4; C1 / 4] ]) with (list2D_to_matrix
         [ [-C1 / 4; -C1 / 4; -C1 / 4; -C1 / 4]; [-C1 / 4; -C1 / 4; -C1 / 4; -C1 / 4]; [-C1 / 4; -C1 / 4; -C1 / 4; -C1 / 4];
           [-C1 / 4; -C1 / 4; -C1 / 4; -C1 / 4] ]).
  2,4: solve_matrix.
  1:{ unfold WF_Matrix. intros. rewrite WF_list2D_to_matrix. reflexivity. intuition. intros. destruct H0. symmetry in H0. rewrite H0. intuition. inversion H0. symmetry in H1. rewrite H1.  reflexivity. inversion H1. symmetry in H2. 1: rewrite H2. symmetry in H2. reflexivity. inversion H2. symmetry in H3. 1: rewrite H3. symmetry in H3. reflexivity. inversion H3. intuition. } solve_matrix.
  (* repeated; not a lot of ways arounnd it I am afraid, unless every statement is very carefully indexed *)
  3:{ unfold WF_Matrix. intros. unfold scale.
      rewrite WF_list2D_to_matrix. C_field. intuition. intros. destruct H0. symmetry in H0. rewrite H0. intuition. inversion H0. symmetry in H1. rewrite H1.  reflexivity. inversion H1. symmetry in H2. 1: rewrite H2. symmetry in H2. reflexivity. inversion H2. symmetry in H3. 1: rewrite H3. symmetry in H3. reflexivity. inversion H3. intuition. } solve_matrix.

  unfold WF_Matrix. intros. rewrite WF_list2D_to_matrix. reflexivity. intuition. intros. destruct H0. symmetry in H0. rewrite H0. intuition. inversion H0. symmetry in H1. rewrite H1.  reflexivity. inversion H1. symmetry in H2. 1: rewrite H2. symmetry in H2. reflexivity. inversion H2. symmetry in H3. 1: rewrite H3. symmetry in H3. reflexivity. inversion H3. intuition. solve_matrix.
  unfold WF_Matrix. intros. rewrite WF_list2D_to_matrix. reflexivity. intuition. intros. destruct H0. symmetry in H0. rewrite H0. intuition. inversion H0. symmetry in H1. rewrite H1.  reflexivity. inversion H1. symmetry in H2. 1: rewrite H2. symmetry in H2. reflexivity. inversion H2. symmetry in H3. 1: rewrite H3. symmetry in H3. reflexivity. inversion H3. intuition. solve_matrix.
  unfold WF_Matrix. intros. unfold scale. rewrite WF_list2D_to_matrix. C_field. intuition. intros. destruct H0. symmetry in H0. rewrite H0. intuition. inversion H0. symmetry in H1. rewrite H1.  reflexivity. inversion H1. symmetry in H2. 1: rewrite H2. symmetry in H2. reflexivity. inversion H2. symmetry in H3. 1: rewrite H3. symmetry in H3. reflexivity. inversion H3. intuition. solve_matrix.
  unfold WF_Matrix. intros. rewrite WF_list2D_to_matrix. reflexivity. intuition. intros. destruct H0. symmetry in H0. rewrite H0. intuition. inversion H0. symmetry in H1. rewrite H1.  reflexivity. inversion H1. symmetry in H2. 1: rewrite H2. symmetry in H2. reflexivity. inversion H2. symmetry in H3. 1: rewrite H3. symmetry in H3. reflexivity. inversion H3. intuition. solve_matrix.
  unfold WF_Matrix. intros. rewrite WF_list2D_to_matrix. reflexivity. intuition. intros. destruct H0. symmetry in H0. rewrite H0. intuition. inversion H0. symmetry in H1. rewrite H1.  reflexivity. inversion H1. symmetry in H2. 1: rewrite H2. symmetry in H2. reflexivity. inversion H2. symmetry in H3. 1: rewrite H3. symmetry in H3. reflexivity. inversion H3. intuition. solve_matrix.
  unfold WF_Matrix. intros. rewrite WF_list2D_to_matrix. reflexivity. intuition. intros. destruct H0. symmetry in H0. rewrite H0. intuition. inversion H0. symmetry in H1. rewrite H1.  reflexivity. inversion H1. symmetry in H2. 1: rewrite H2. symmetry in H2. reflexivity. inversion H2. symmetry in H3. 1: rewrite H3. symmetry in H3. reflexivity. inversion H3. intuition. 
   rewrite inductive_expr.
   symmetry.
   rewrite inductive_expr.
   apply cong_eq.
   symmetry.
   apply IHr.
Qed.

(------------------------------------------------------------------------------------)
(------------------------------------------------------------------------------------)
Failed or unnecessary lemmas to be taken up later, possibly:

Lemma small_grover_general_correct_prob_1_3  : forall (r:nat) g, In g f_list -> (r > 0)%nat -> (r < 4)%nat ->
    Rsum 4 (fun z => if g z 
              then (@prob_partial_meas_matrix 2 0
    (basis_matrix_4 z)
    (denote (small_grover_general_i_rots g r) (denote equal_superposition (I 1)))) else 0)
               = 
                 ((sin ( INR (2 * r + 1) * asin (√ (INR (count g 0 (4)) / 4)))) ^ 2)%R.
Proof.
  intros.
  induction r.
  inversion H0.
  induction r.
  replace ((⟦ small_grover_general_i_rots g 1 ⟧) ((⟦ equal_superposition ⟧) (I 1))) with ((⟦ small_grover_total g⟧) (I 1)).
  2:  symmetry; apply small_grover_general_rot_equality; apply H.
  apply Grover2QubitGeneral.small_grover_general_correct_prob_simpl; apply H.
  destruct r.
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
  unfold Rsum, sum_f_R0, count. simpl; unfold prob_partial_meas_matrix. replace ((sin ((1 + 1 + 1 + 1 + 1) * asin (√ (1 / 4))) * (sin ((1 + 1 + 1 + 1 + 1) * asin (√ (1 / 4))) * 1))%R) with (sin ( INR (2 * 2 + 1) * asin (√ (1 / 4))) ^ 2)%R.
  2: { simpl. replace (2 * 2 + 1)%R with (1 + 1 + 1 + 1 + 1)%R by R_field. reflexivity. }
  rewrite one_true_trig_2.
  R_field_simplify.
  replace (denote_box true (small_grover_general_i_rots (fs [0%nat]) 2) (denote_box true equal_superposition (I 1))) with (list2D_to_matrix ( [ [  (RtoC (1 / 4)) ;  (RtoC ((1/4))) ;  (RtoC (-(1 / 4))) ;   (RtoC (-(1/4))) ] ; [   (RtoC ((1/4)));  (RtoC (1 / 4))  ;  (RtoC (-(1/4))) ; (RtoC (-(1 / 4)))  ]  ; [ (RtoC (-(1 / 4)))  ;  (RtoC (-(1/4))) ; (RtoC ((1 / 4)))  ;  (RtoC ((1/4))) ] ; [   (RtoC (-(1/4))) ; (RtoC (-(1 / 4))) ;  (RtoC ((1/4)));  (RtoC (1 / 4)) ] ] ))%M. 2: symmetry; apply small_grover_2_rots_0.
  solve_matrix. R_field. Admitted.
  
Definition operator_single_rot_0 : Square 4 :=
        (list2D_to_matrix ( [ [ ((1/2)); (-(1/2)) ; (-(1/2)) ; (1/2) ] ; [ (1/2) ; (-(1/2)) ;(1/2); (1/2)]  ; [ (1/2) ; (1/2) ; (-(1/2)) ; (1/2) ] ; [ (1/2) ; (1/2) ; (1/2) ; (-(1/2)) ] ] )).

Lemma small_grover_r_single_op: forall (r:nat) (s:Square 4), WF_Matrix s -> (r > 0)%nat ->

    super (unitary_op_0) (denote (small_grover_iterate_0 r) s)
               = 
                 (denote (small_grover_iterate_0 (S r))) s.
Proof.  
  intros.
  destruct r.
  inversion H0.
  destruct r.
  unfold operator_single_rot_0.
  
  matrix_denote.
  Msimpl.
  admit.
  solve_matrix.
  destruct (fs [0%nat] 0), (fs [0%nat] 1), (fs [0%nat] 2),  (fs [0%nat] 3).
  1: rewrite small_grover_general_rot_equality.
  replace ((⟦ small_grover_total (fs [0%nat]) ⟧) (I 1)) with (list2D_to_matrix ( [ [ C1 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] )).
  2: symmetry. 2: apply Grover2QubitGeneral.prob_matrix_0.
  unfold super.
  matrix_denote.
  solve_matrix.
  all: try C_field_simplify. all: try replace ((/ C2) ^* ) with (/ C2). all: try C_field_simplify. all: try reflexivity.
  


  Lemma small_grover_rotations_single_op: forall (r:nat) g, In g f_list -> (r > 0)%nat ->

    super (match_operator_single_rot g) (denote (small_grover_general_i_rots g r) (I 1))
               = 
                 (denote (small_grover_general_i_rots g (S r))) (I 1).
Lemma small_grover_general_periodic : forall (r:nat) g, In g f_list -> (r > 0)%nat ->

    (denote (small_grover_general_i_rots g r) (I 1))
               = 
                 (denote (small_grover_general_i_rots g (S (S (S (S (S (S r)))))) ) (I 1)).
Proof.
  intros.
  destruct r.
  inversion H0.
  destruct r.
  rewrite small_grover_general_rot_equality.
  2: apply H.
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
   again, rewrite does not recognize the appropriate terms, unfortunately. 
  1: { replace((⟦ small_grover_total (fs [0%nat]) ⟧) (I 1))  with(list2D_to_matrix ( [ [ C1 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] )).
  2: symmetry. 2: apply Grover2QubitGeneral.prob_matrix_0. matrix_denote. symmetry. Msimpl. solve_matrix.
       
  
Lemma small_grover_general_correct_prob  : forall (r:nat) g, In g f_list -> (r > 0)%nat ->
    Rsum 4 (fun z => if g z 
              then (@prob_partial_meas_matrix 2 0
    (basis_matrix_4 z)
    (denote (small_grover_general_r_rots g r) (I 1))) else 0)
               = 
                 ((sin ( INR (2 * r + 1) * asin (√ (INR (count g 0 (4)) / 4)))) ^ 2)%R.
Proof.
  intros.
  induction r.
  inversion H0.
  induction r.
  replace ((⟦ small_grover_general_i_rots g 1 ⟧) (I 1)) with ((⟦ small_grover_total g⟧) (I 1)).
  2:  symmetry; apply small_grover_general_correct_prob_simpl; apply H.
  apply Grover2QubitGeneral.small_grover_general_correct_prob_simpl; apply H.
  
  replace




Lemma small_grover_general_periodic : forall (r:nat) g, In g f_list -> (r > 0)%nat ->

    (denote (small_grover_general_i_rots g r) (I 1))
               = 
                 (denote (small_grover_general_i_rots g (S (S r)) ) (I 1)).
Proof.
  intros.
  destruct r.
  inversion H0.
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
  1: { matrix_denote. solve_matrix.


Lemma small_grover_2_rots_0 : 
  denote (small_grover_general_i_rots (fs [0%nat]) 2) (denote equal_superposition (I 1)) =  list2D_to_matrix ( [ [  (RtoC (1 / 4)) ;  (RtoC ((1/4))) ;  (RtoC (-(1 / 4))) ;   (RtoC (-(1/4))) ] ; [   (RtoC ((1/4)));  (RtoC (1 / 4))  ;  (RtoC (-(1/4))) ; (RtoC (-(1 / 4)))  ]  ; [ (RtoC (-(1 / 4)))  ;  (RtoC (-(1/4))) ; (RtoC ((1 / 4)))  ;  (RtoC ((1/4))) ] ; [   (RtoC (-(1/4))) ; (RtoC (-(1 / 4))) ;  (RtoC ((1/4)));  (RtoC (1 / 4)) ] ] ).
Proof.
  matrix_denote.
  Msimpl.
Admitted.

Lemma super_over_denotation_0: forall s r,
                                 super (list2D_to_matrix [ [  (RtoC (1 / 4)) ;  (RtoC ((1/4))) ;  (RtoC (-(1 / 4))) ;   (RtoC (-(1/4))) ] ; [   (RtoC (-(1/4)));  (RtoC (1 / 4))  ;  (RtoC (-(1/4))) ; (RtoC (-(1 / 4)))  ]  ; [ (RtoC ((1 / 4)))  ;  (RtoC ((1/4))) ; (RtoC (-(1 / 4)))  ;  (RtoC ((1/4))) ] ; [   (RtoC ((1/4))) ; (RtoC ((1 / 4))) ;  (RtoC ((1/4)));  (RtoC (-(1 / 4)))] ] ) (denote (small_grover_general_i_rots (fs [0%nat]) (r)) s) =
                                   (denote (small_grover_general_i_rots (fs [0%nat]) (S r)) s).
Proof.
   destruct r. matrix_denote. solve_matrix.
*)
