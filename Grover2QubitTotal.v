Require Import Nat.
Require Import DBCircuits.
Require Import TypeChecking.
Require Import Denotation.
Require Import Composition.
Require Import VectorDef.
Require Import sin_asin_rules.
Require Import Coq.Lists.List.
Require Import QuantumLib.VectorStates.
Require Import QuantumLib.Measurement.
Require Import QuantumLib.Matrix.
Require Import QuantumLib.FTA.
Require Import Grover2QubitBasic.


Local Coercion Nat.b2n : bool >-> nat.

(*has to be declared anew*)
Variable f : nat -> bool.
    
Local Open Scope nat_scope.

(* since In goes to Prop, we need this; this is an instance of existsb so its correctness is reliant on the correctness of existsb, see List, and of the boolean valued equivalence function. *)
Fixpoint is_in (k:nat) (l:list nat) : bool := existsb (fun x => (x =? k)) l.

(* Function to generate functions *)
Definition fs (l:list nat) : nat -> bool :=
  (fun g => match g with
         | 0 => is_in 0 l  
         | 1 => is_in 1 l
         | 2 => is_in 2 l
         | 3 => is_in 3 l
         | _ => false
         end).

(* We want it to generate functions so that for whichever arguments it is given below 4, the generated function returns true for, and for any others, false*)
Lemma correct_fs: forall l g, (g < 4)%nat -> (is_in g l = true -> (fs l) g = true) /\ (is_in g l = false -> (fs l) g = false).
Proof. intros.
       destruct g. split. intros. unfold fs. apply H0. intros. apply H0.
       destruct g. split. intros. unfold fs. apply H0. intros. apply H0.
       destruct g. split. intros. unfold fs. apply H0. intros. apply H0.
       destruct g. split. intros. unfold fs. apply H0. intros. apply H0.
       inversion H. inversion H1. inversion H3. inversion H5. inversion H7.
Qed.
Local Close Scope nat_scope.

(*This was in the end unused; S gate is derived from the The "controlled phase gate" _R_ m with m = 2, so the rotation = Pi/2
Definition _S := _R_ (PI/2).*)

Local Close Scope nat_scope.

Local Open Scope circ_scope.

(* slightly more convenient tactic in some contexts, adds complex simplification within iterations; amost identical to original in QuantumLib (Rand and contributors)*)
Ltac crunch_matrix_new := 
                    match goal with 
                      | [|- ?G ] => idtac "Crunching:" G
                      end;
                      repeat match goal with
                             | [ c : C |- _ ] => cbv [c]; clear c; try C_field_simplify; try C_field (* 'unfold' hangs *)
                             end; 
                      simpl;
                      unfold list2D_to_matrix;    
                      autounfold with U_db;
                      prep_matrix_equality;
                      simpl;
                      destruct_m_eq';
                      simpl;
                    Csimpl; (* basic rewrites only *)
                    try C_field_simplify; try C_field;
                      try reflexivity;
                     try solve_out_of_bounds.
(* as above *)
Ltac solve_matrix_new := assoc_least;
                     repeat reduce_matrix; try crunch_matrix_new;
                     (* handle out-of-bounds *)
                     unfold Nat.ltb; simpl; try rewrite andb_false_r; 
                     (* try to solve complex equalities *)
                     autorewrite with C_db; try lca.

(* very ismple lemma that successive applications of circuits are composite *)
Lemma denote_succ : forall {n} W (b1 b2 : Box W W) (a: Square n) (b: Square n), denote b1 = super a -> denote b2 = super b -> (fun s => (denote b1 ) (denote b2 s)) =  (fun s => (super a) (super b s)).
Proof. intros. replace (⟦ b2 ⟧) with (super b). replace (⟦ b1 ⟧) with (super a). reflexivity. Qed.

(* Definition of the oracle for two marked elements, the 0th and 1st in this case; same naming for others below *)
Definition small_oracle_0_1 : Box ( Qubit ⊗ Qubit ) ( Qubit ⊗ Qubit ) :=
  box_ (x, y) ⇒
    let_ y ← _Z $ y;   
    let_ y ← _X $ y;
    let_ x ← _X $ x;   
    let_ y ← _Z $ y;
    let_ x ← _Z $ x;
    let_ y ← _X $ y;
    let_ x ← _X $ x;  
    (x,y).

(* correctness lemma for oracle with two solutions; in this case, for the one marking the 0th and 1st states. Same naming for others below *)
Lemma correct_small_oracle_0_1 : forall (s: Square 4), WF_Matrix s -> denote (small_oracle_0_1) s = super (list2D_to_matrix ( [ [ (-C1) ; C0 ; C0 ; C0 ] ; [ C0 ; (-C1); C0; C0 ] ; [ C0 ; C0 ; C1 ;C0 ] ; [C0 ; C0; C0 ; C1] ] )) s.
Proof.
  matrix_denote.
  solve_matrix.
Qed.
    
(* Transitivity of equality, already defined, also depricated here *)
Lemma eq_trans: forall (A:Set) (x:A) (y:A) (z:A), (x = y) -> (y = z) -> (x = z).
Proof.
  intros.
  rewrite H0 in H.
  apply H.
Qed.

(* oracle for f02 *)
Definition small_oracle_0_2 : Box ( Qubit ⊗ Qubit ) ( Qubit ⊗ Qubit ) :=
   box_ (x, y) ⇒
    let_ y ← _Z $ y;   
    let_ y ← _X $ y;
    let_ x ← _X $ x;   
    let_ y ← _Z $ y;
    let_ x ← _Z $ x;
    let_ y ← _X $ y;
    let_ x ← _X $ x;
    let_ y ← _Z $ y;
    let_ x ← _Z $ x;
    (x,y).

(*correctness lemma for oracle above *)
Lemma correct_small_oracle_0_2 : forall (s: Square 4), WF_Matrix s -> denote (small_oracle_0_2) s = super (list2D_to_matrix ( [ [ (-C1) ; C0 ; C0 ; C0 ] ; [ C0 ; C1; C0; C0 ] ; [ C0 ; C0 ; (-C1) ;C0 ] ; [C0 ; C0; C0 ; C1] ] )) s.
Proof.
  matrix_denote.
  solve_matrix.
Qed.

(* oracle for f03*)
Definition small_oracle_0_3 : Box ( Qubit ⊗ Qubit ) ( Qubit ⊗ Qubit ) :=
  box_ (x, y) ⇒
    let_ x ← _Z $ x;
    let_ y ← _Z $ y;
    let_ x ← _X $ x;
    let_ y ← _X $ y;
    let_ x ← _Z $ x;
    let_ y ← _Z $ y;
    let_ x ← _X $ x;
    let_ y ← _X $ y;
    let_ x ← _Z $ x;
    let_ y ← _Z $ y;
    (x,y).

(*correctness lemma for oracle above *)
Lemma correct_small_oracle_0_3 : forall (s: Square 4), WF_Matrix s -> denote (small_oracle_0_3) s = super (list2D_to_matrix ( [ [ (-C1) ; C0 ; C0 ; C0 ] ; [ C0 ; C1; C0; C0 ] ; [ C0 ; C0 ; C1 ;C0 ] ; [C0 ; C0; C0 ; (-C1)] ] )) s.
Proof.
  matrix_denote.
  solve_matrix.
Qed.

(*oracle for f12 *)
Definition small_oracle_1_2 : Box ( Qubit ⊗ Qubit ) ( Qubit ⊗ Qubit ) :=
  box_ (x, y) ⇒
    let_ x ← _Z $ x;
    let_ y ← _Z $ y;
    (x,y).
 
(*correctness lemma for oracle above *)
Lemma correct_small_oracle_1_2 : forall (s: Square 4), WF_Matrix s -> denote (small_oracle_1_2) s = super (list2D_to_matrix ( [ [ C1 ; C0 ; C0 ; C0 ] ; [ C0 ; (RtoC (-1)); C0; C0 ] ; [ C0 ; C0 ;(RtoC (-1)) ;C0 ] ; [C0 ; C0; C0 ; C1] ] )) s.
Proof.
  matrix_denote.
  solve_matrix.
Qed.

(*oracle for f13*)
Definition small_oracle_1_3 : Box ( Qubit ⊗ Qubit ) ( Qubit ⊗ Qubit ) :=
  box_ (x, y) ⇒
    let_ y  ← _Z $ y;
    (x,y).

Lemma correct_small_oracle_1_3 : forall (s: Square 4), WF_Matrix s -> denote (small_oracle_1_3) s = super (list2D_to_matrix ( [ [ (C1) ; C0 ; C0 ; C0 ] ; [ C0 ; (-C1); C0; C0 ] ; [ C0 ; C0 ; (C1) ;C0 ] ; [C0 ; C0; C0 ; (-C1)] ] )) s.
Proof.
  matrix_denote.
  solve_matrix.
Qed.  

(*oracle for f23*)
Definition small_oracle_2_3 : Box ( Qubit ⊗ Qubit ) ( Qubit ⊗ Qubit ) :=
  box_ (x, y) ⇒
    let_ x ← _Z $ x;
    (x,y).

Lemma correct_small_oracle_2_3 : forall (s: Square 4), WF_Matrix s -> denote (small_oracle_2_3) s = super (list2D_to_matrix ( [ [ (C1) ; C0 ; C0 ; C0 ] ; [ C0 ; (C1); C0; C0 ] ; [ C0 ; C0 ; (-C1) ;C0 ] ; [C0 ; C0; C0 ; (-C1)] ] )) s.
Proof.
  matrix_denote.
  solve_matrix.
Qed.

Lemma involutory_small_oracle_2_3 : forall (s: Square 4), WF_Matrix s -> denote (small_oracle_2_3) ((denote (small_oracle_2_3)) s) = denote (@id_circ  ( Qubit ⊗ Qubit ) ) s.
Proof.
  intros.
  matrix_denote.
  solve_matrix.
Qed.

(*oracle for f012*)
Definition small_oracle_0_1_2 : Box ( Qubit ⊗ Qubit ) ( Qubit ⊗ Qubit ) :=
  box_ (x, y) ⇒
    let_ (x,y) ← small_oracle_0 $ (x,y);
    let_ (x,y) ← small_oracle_1_2 $ (x,y);
    (x,y).

Lemma involutory_small_oracle_0_1_2 : forall (s: Square 4), WF_Matrix s -> denote (small_oracle_0_1_2) ((denote (small_oracle_0_1_2)) s) = denote (@id_circ  ( Qubit ⊗ Qubit ) ) s.
Proof.
  intros.
  matrix_denote.
  solve_matrix.
Qed.

Lemma correct_small_oracle_0_1_2 : forall (s: Square 4), WF_Matrix s -> denote (small_oracle_0_1_2) s = super (list2D_to_matrix ( [ [ (-C1) ; C0 ; C0 ; C0 ] ; [ C0 ; (-C1); C0; C0 ] ; [ C0 ; C0 ; (-C1) ;C0 ] ; [C0 ; C0; C0 ; C1] ] )) s.
Proof.
  matrix_denote.
  solve_matrix.
Qed.

(*oracle for f123*)
Definition small_oracle_1_2_3 : Box ( Qubit ⊗ Qubit ) ( Qubit ⊗ Qubit ) :=
  box_ (x, y) ⇒
    let_ (x,y) ← small_oracle_3 $ (x,y);
    let_ (x,y) ← small_oracle_1_2 $ (x,y);
    (x,y).

Lemma involutory_small_oracle_1_2_3 : forall (s: Square 4), WF_Matrix s -> denote (small_oracle_1_2_3) ((denote (small_oracle_1_2_3)) s) = denote (@id_circ  ( Qubit ⊗ Qubit ) ) s.
Proof.
  intros.
  matrix_denote.
  solve_matrix.
Qed.

Lemma correct_small_oracle_1_2_3 : forall (s: Square 4), WF_Matrix s -> denote (small_oracle_1_2_3) s = super (list2D_to_matrix ( [ [ C1 ; C0 ; C0 ; C0 ] ; [ C0 ; (-C1); C0; C0 ] ; [ C0 ; C0 ; (-C1) ;C0 ] ; [C0 ; C0; C0 ; (-C1)] ] )) s.
Proof.
  matrix_denote.
  solve_matrix.
Qed.

(*oracle for f023*)
Definition small_oracle_0_2_3 : Box ( Qubit ⊗ Qubit ) ( Qubit ⊗ Qubit ) :=
  box_ (x, y) ⇒
    let_ (x,y) ← small_oracle_0 $ (x,y);
    let_ (x,y) ← small_oracle_2_3 $ (x,y);
    (x,y).

Lemma involutory_small_oracle_0_2_3 : forall (s: Square 4), WF_Matrix s -> denote (small_oracle_0_2_3) ((denote (small_oracle_0_2_3)) s) = denote (@id_circ  ( Qubit ⊗ Qubit ) ) s.
Proof.
  intros.
  matrix_denote.
  solve_matrix.
Qed.

Lemma correct_small_oracle_0_2_3 : forall (s: Square 4), WF_Matrix s -> denote (small_oracle_0_2_3) s = super (list2D_to_matrix ( [ [ (-C1) ; C0 ; C0 ; C0 ] ; [ C0 ; C1; C0; C0 ] ; [ C0 ; C0 ; (-C1) ;C0 ] ; [C0 ; C0; C0 ; (-C1)] ] )) s.
Proof.
  matrix_denote.
  solve_matrix.
Qed.

(*oracle for f013*)
Definition small_oracle_0_1_3 : Box ( Qubit ⊗ Qubit ) ( Qubit ⊗ Qubit ) :=
  box_ (x, y) ⇒
    let_ (x,y) ← small_oracle_0 $ (x,y);
    let_ (x,y) ← small_oracle_1_3 $ (x,y);
    (x,y).

Lemma involutory_small_oracle_0_1_3 : forall (s: Square 4), WF_Matrix s -> denote (small_oracle_0_1_3) ((denote (small_oracle_0_1_3)) s) = denote (@id_circ  ( Qubit ⊗ Qubit ) ) s.
Proof.
  intros.
  matrix_denote.
  solve_matrix.
Qed.

Lemma correct_small_oracle_0_1_3 : forall (s: Square 4), WF_Matrix s -> denote (small_oracle_0_1_3) s = super (list2D_to_matrix ( [ [ (-C1) ; C0 ; C0 ; C0 ] ; [ C0 ; (-C1); C0; C0 ] ; [ C0 ; C0 ; C1 ;C0 ] ; [C0 ; C0; C0 ; (-C1)] ] )) s.
Proof.
  matrix_denote.
  solve_matrix.
Qed.


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
       (let_ (x,y) ← small_oracle_0_1 $ (x,y);
        let_ (x,y) ← small_diffusion $ (x,y);
        (x,y))
  |true, false, true, false =>
        (let_ (x,y) ← small_oracle_0_2 $ (x,y);
        let_ (x,y) ← small_diffusion $ (x,y);
        (x,y))
  |true, false, false, true =>
       (let_ (x,y) ← small_oracle_0_3 $ (x,y);
        let_ (x,y) ← small_diffusion $ (x,y);
        (x,y))
  |false, true, true, false => 
        (let_ (x,y) ← small_oracle_1_2 $ (x,y);
        let_ (x,y) ← small_diffusion $ (x,y);
        (x,y))
  |false, true, false, true =>
       (let_ (x,y) ← small_oracle_1_3 $ (x,y);
        let_ (x,y) ← small_diffusion $ (x,y);
        (x,y))
  |false, false, true, true =>
       (let_ (x,y) ← small_oracle_2_3 $ (x,y);
        let_ (x,y) ← small_diffusion $ (x,y);
        (x,y))
  |true, true, true, false =>
     (let_ (x,y) ← small_oracle_0_1_2 $ (x,y);
      let_ (x,y) ← small_diffusion $ (x,y);
      (x,y))
  |true, true, false, true =>
      (let_ (x,y) ← small_oracle_0_1_3 $ (x,y);
       let_ (x,y) ← small_diffusion $ (x,y);
       (x,y))
  |false, true, true, true =>
      (let_ (x,y) ← small_oracle_1_2_3 $ (x,y);
       let_ (x,y) ← small_diffusion $ (x,y);
       (x,y))
  |true, false, true, true =>
      (let_ (x,y) ← small_oracle_0_2_3 $ (x,y);
       let_ (x,y) ← small_diffusion $ (x,y);
       (x,y))
  | _, _, _, _ => (x,y)
                              
                              
  
     end.

Lemma small_grover_total_WT : Typed_Box (small_grover_total f).
Proof. type_check. Qed.

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
(* Correctness lemmas for single iterations ---------------------------------------------------------------------------------------------------------------------*)
(*Unfortunately, the previous lemmas cannot be used in this proof (without making them significantly more convoluted), because denotation (denote_box) cannot really be pused to the inside *)
Lemma prob_matrix_0 : denote (small_grover_total (fs [0%nat])) (I 1) = list2D_to_matrix ( [ [ C1 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] ).
Proof.
  unfold small_grover_total.
  all: grover_2qubit_denote_to_nonzero_general.
    Local Close Scope circ_scope.
  apply Csqrt2_neq_0.
  grover_nonzero_begin.
  grover_nonzero_end.
  apply sqrt_sqrt;
  intuition.
Qed.


Lemma prob_matrix_1 : denote (small_grover_total  (fs [1%nat])) (I 1) = list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C1 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] ) .
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
  These separate lemmas are not necessary, the relevant part of their meaning is encapsulated in the main lemma,
  however, they make that lemma much quicker and more transparent itself to prove, and also a lot neater (since it is already quite long). *)
Lemma prob_matrix_1_2 :  denote (small_grover_total (fs ([1%nat;2%nat]))) (I 1) = list2D_to_matrix ( [ [  (RtoC (1 / 4)) ;  (RtoC (-(1/4))) ;  (RtoC (-(1 / 4))) ;   (RtoC ((1/4))) ] ; [   (RtoC (-(1/4)));  (RtoC (1 / 4))  ;  (RtoC ((1/4))) ; (RtoC (-(1 / 4)))  ]  ; [ (RtoC (-(1 / 4)))  ;  (RtoC ((1/4))) ; (RtoC ((1 / 4)))  ;  (RtoC (-(1/4))) ] ; [   (RtoC ((1/4))) ; (RtoC (-(1 / 4))) ;  (RtoC (-(1/4)));  (RtoC (1 / 4)) ] ] ).
  matrix_denote.
  solve_matrix.
  all: repeat rewrite Cexp_PI2.
  all: solve_matrix.
  all: C_field_simplify; solve_matrix.
  all: C_field.
Qed.

Lemma prob_matrix_0_3 : denote (small_grover_total (fs ([0%nat;3%nat]))) (I 1) = list2D_to_matrix ( [ [  (RtoC (1 / 4)) ; (RtoC (-(1/4))) ;(RtoC (-(1/4))) ;  (RtoC (1 / 4)) ] ; [ (RtoC (-(1/4))) ; (RtoC (1 / 4)) ;  (RtoC (1 / 4)) ; (RtoC (-(1/4))) ]  ; [ (RtoC (-(1/4))) ; (RtoC (1 / 4)) ; (RtoC (1 / 4))  ; (RtoC (-(1/4))) ] ; [  (RtoC (1 / 4))  ;(RtoC (-(1/4))) ; (RtoC (-(1/4))) ;  (RtoC (1 / 4)) ] ] ).
  matrix_denote.
  solve_matrix.
  all: repeat rewrite Cexp_PI2.
  all:  solve_matrix.
  all: C_field_simplify; solve_matrix. 
  all: C_field.
Qed.

Lemma prob_matrix_0_1 : denote (small_grover_total (fs ([0%nat;1%nat]))) (I 1) =  list2D_to_matrix ( [ [  (RtoC (1 / 4)) ;  (RtoC ((1/4))) ;  (RtoC (-(1 / 4))) ;   (RtoC (-(1/4))) ] ; [   (RtoC ((1/4)));  (RtoC (1 / 4))  ;  (RtoC (-(1/4))) ; (RtoC (-(1 / 4)))  ]  ; [ (RtoC (-(1 / 4)))  ;  (RtoC (-(1/4))) ; (RtoC ((1 / 4)))  ;  (RtoC ((1/4))) ] ; [   (RtoC (-(1/4))) ; (RtoC (-(1 / 4))) ;  (RtoC ((1/4)));  (RtoC (1 / 4)) ] ] ).
  matrix_denote.
  solve_matrix.
  all: repeat rewrite Cexp_PI2.
  all:  solve_matrix.
  all: C_field_simplify; solve_matrix.
  all: C_field.
Qed.

Lemma prob_matrix_0_2 : denote (small_grover_total (fs ([0%nat;2%nat]))) (I 1) = list2D_to_matrix ( [ [  (RtoC (1 / 4)) ;  (RtoC (-(1/4))) ;  (RtoC ((1 / 4))) ;   (RtoC (-(1/4))) ] ; [   (RtoC (-(1/4)));  (RtoC (1 / 4))  ;  (RtoC (-(1/4))) ; (RtoC ((1 / 4)))  ]  ; [ (RtoC ((1 / 4)))  ;  (RtoC (-(1/4))) ; (RtoC ((1 / 4)))  ;  (RtoC (-(1/4))) ] ; [   (RtoC (-(1/4))) ; (RtoC ((1 / 4))) ;  (RtoC (-(1/4)));  (RtoC (1 / 4)) ] ] ).
  matrix_denote.
  solve_matrix.
  all: repeat rewrite Cexp_PI2.
  all:  solve_matrix.
  all: C_field_simplify; solve_matrix.
  all: C_field.
Qed.

Lemma prob_matrix_2_3 : denote (small_grover_total (fs ([2%nat;3%nat]))) (I 1) = 
list2D_to_matrix ( [ [  (RtoC (1 / 4)) ;  (RtoC ((1/4))) ;  (RtoC (-(1 / 4))) ;   (RtoC (-(1/4))) ] ; [   (RtoC ((1/4)));  (RtoC (1 / 4))  ;  (RtoC (-(1/4))) ; (RtoC (-(1 / 4)))  ]  ; [ (RtoC (-(1 / 4)))  ;  (RtoC (-(1/4))) ; (RtoC ((1 / 4)))  ;  (RtoC ((1/4))) ] ; [   (RtoC (-(1/4))) ; (RtoC (-(1 / 4))) ;  (RtoC ((1/4)));  (RtoC (1 / 4)) ] ] ).
  matrix_denote.
  solve_matrix.
  all: repeat rewrite Cexp_PI2.
  all:  solve_matrix.
  all: C_field_simplify; solve_matrix.
  all: C_field.
Qed.

Lemma prob_matrix_1_3 : denote (small_grover_total (fs ([1%nat;3%nat]))) (I 1) = list2D_to_matrix ( [ [  (RtoC (1 / 4)) ; (RtoC (-(1/4))) ;(RtoC ((1/4))) ;  (RtoC (-(1 / 4))) ] ; [ (RtoC (-(1/4))) ; (RtoC (1 / 4)) ;  (RtoC (-(1 / 4))) ; (RtoC ((1/4))) ]  ; [ (RtoC ((1/4))) ; (RtoC (-(1 / 4))) ; (RtoC (1 / 4))  ; (RtoC (-(1/4))) ] ; [  (RtoC (-(1 / 4))) ; (RtoC ((1/4))) ; (RtoC (-(1/4))) ;  (RtoC (1 / 4)) ] ] ).
  matrix_denote.
  solve_matrix.
  all: repeat rewrite Cexp_PI2.
  all:  solve_matrix.
  all: C_field_simplify; solve_matrix.
  all: C_field.
Qed.

Lemma prob_matrix_1_2_3: denote (small_grover_total (fs [1%nat; 2%nat; 3%nat])) (I 1) = list2D_to_matrix ( [ [ C1 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] ).
Proof.
  all: grover_2qubit_denote_to_nonzero_general.
  all: C_field.
Qed.


Lemma prob_matrix_0_2_3 : denote (small_grover_total  (fs [0%nat; 2%nat; 3%nat])) (I 1) = list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C1 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] ).
Proof.
  grover_2qubit_denote_to_nonzero_general.
  all: C_field.
Qed.

Lemma prob_matrix_0_1_3: denote (small_grover_total (fs [0%nat; 1%nat; 3%nat])) (I 1) = list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C1 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] ).
Proof.
  grover_2qubit_denote_to_nonzero_general.
  all: C_field.
Qed.

Lemma prob_matrix_0_1_2 : denote (small_grover_total (fs [0%nat; 1%nat; 2%nat])) (I 1) =  list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C1 ] ] ).
Proof.
  grover_2qubit_denote_to_nonzero_general.
  all: C_field.
Qed.

(*-----------------------------------------------------------------------------------------------------------------------------------------------------------------------*)
Local Close Scope nat_scope.

(*counts the number of solutions for a given f, taken from SQIR*)
Fixpoint count (f : nat -> bool) a b : nat :=
  match b with
  | O => O
  | S b' => (f (a + b') + count f a b')%nat
  end.

(*so as not to have to construct the relevant matrices to use as observablees from outer products of basis-vectors; dpericated, because an explicit definition is easier do deal with in the proof *)
Definition basis_matrix (n:nat) (k:nat) : Matrix n n :=
  (fun i j => if (i =? k)%nat && (j =? k)%nat then C1 else C0).

(*explicitness, although it looks worse, is a lot easier to deal with below due t+o the non-dimension-preserving nature of the basic definition here below*)
Definition basis_matrix_4 (k:nat) : Matrix 4 4 :=
  match k with
  | 0%nat => list2D_to_matrix ( [ [ C1 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] )
  | 1%nat => list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C1 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] )
  | 2%nat => list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C1 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] )
  | 3%nat => list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C1 ] ] )
  | _ => basis_matrix 4 k (* let the absract definition deal with it; will be a Zero 4 *)                
  end.

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
  unfold exp_val_meas_matrix;
  solve_matrix;
  ring.

Local Open Scope nat_scope.
Definition f_list : list (nat->bool) :=
  [ (fs [0]) ; (fs [1]) ; (fs [2]) ; (fs [3]) ; (fs [0;1]) ; (fs [0;2]) ; (fs [0;3]) ; (fs [1;2]) ; (fs [1;3]) ; (fs [2;3]); (fs [0;1;2]) ; (fs [0;1;3]) ;(fs [0;2;3]); (fs [1;2;3]) ].              
Local Close Scope nat_scope.

Lemma small_grover_total_correct_prob_simpl : forall g, In g f_list -> Rsum 4 (fun z => if g z 
              then (@exp_val_meas_matrix 2 (basis_matrix_4 z) (denote (small_grover_total g) (I 1)))
              else 0)
               = 
                 ((sin ((2 * 1 + 1) * asin (√ (INR (count g 0 (4)) / 4)))) ^ 2)%R.
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
  
  (* unfortunately, rewrite does not find the relevant sections in the subgoals to do the below automatically, even though that is why the lemmas are reversed in this implementation; thus it must be done manually. *)
  
  1: replace((⟦ small_grover_total (fs [0%nat]) ⟧) (I 1))  with(list2D_to_matrix ( [ [ C1 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] )).
  2: symmetry. 2: apply prob_matrix_0.
  2: replace((⟦ small_grover_total (fs [1%nat]) ⟧) (I 1))  with(list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C1 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] )).
  3: symmetry; apply prob_matrix_1.
  3: replace((⟦ small_grover_total (fs [2%nat]) ⟧) (I 1))  with(list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C1 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] )).
  4: symmetry. 4: apply prob_matrix_2.
  4: replace((⟦ small_grover_total (fs [3%nat]) ⟧) (I 1))  with(list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C1 ] ] )).  5: symmetry. 5: apply prob_matrix_3.
  1,2,3,4 :  unfold Rsum, sum_f_R0, count; simpl; unfold exp_val_meas_matrix; solve_matrix.
  1,2,3,4: unfold Rminus;  rewrite Rmult_1_l; repeat rewrite Rplus_0_r; repeat rewrite Rplus_0_l; repeat rewrite Rmult_0_l; repeat rewrite Rmult_0_r.
  1,2,3,4: replace (- 0)%R with 0%R. 2,4,6,8: intuition.
  1,2,3,4: repeat rewrite Rplus_0_r; repeat rewrite Rplus_0_l.
  1,2,3,4: replace (2 * 1 + 1)%R with 3%R by ring;
  rewrite sqrt_div_alt.
  2,4,6,8: intuition.
  1,2,3,4: rewrite asin14.
  1,2,3,4: try rewrite Rmult_1_r.
  1,2,3,4: replace (3 * (PI / 6))%R with (1 * (PI / 2))%R.
  all: try repeat rewrite Rmult_1_l.
  all: try rewrite sin_PI2.
  all: try ring.
  1,2,3,4: unfold Rdiv.
  1,2,3,4: symmetry.
  1,2,3,4: rewrite Rmult_comm.
  1,2,3,4:rewrite Rmult_assoc.
  1,2,3,4:replace (/ 6 * 3)%R with (3 * / 6)%R by ring.
  1,2,3,4:replace (3 * / 6)%R with (/ 2)%R.
  all: try R_field_simplify.
  all: try reflexivity.
  1: replace ((⟦ small_grover_total (fs [0%nat; 1%nat]) ⟧) (I 1)) with ( list2D_to_matrix ( [ [  (RtoC (1 / 4)) ;  (RtoC ((1/4))) ;  (RtoC (-(1 / 4))) ;   (RtoC (-(1/4))) ] ; [   (RtoC ((1/4)));  (RtoC (1 / 4))  ;  (RtoC (-(1/4))) ; (RtoC (-(1 / 4)))  ]  ; [ (RtoC (-(1 / 4)))  ;  (RtoC (-(1/4))) ; (RtoC ((1 / 4)))  ;  (RtoC ((1/4))) ] ; [   (RtoC (-(1/4))) ; (RtoC (-(1 / 4))) ;  (RtoC ((1/4)));  (RtoC (1 / 4)) ] ] ) ).
  2: symmetry; apply prob_matrix_0_1.
  2: replace ((⟦ small_grover_total (fs [0%nat; 2%nat]) ⟧) (I 1)) with (list2D_to_matrix ( [ [  (RtoC (1 / 4)) ;  (RtoC (-(1/4))) ;  (RtoC ((1 / 4))) ;   (RtoC (-(1/4))) ] ; [   (RtoC (-(1/4)));  (RtoC (1 / 4))  ;  (RtoC (-(1/4))) ; (RtoC ((1 / 4)))  ]  ; [ (RtoC ((1 / 4)))  ;  (RtoC (-(1/4))) ; (RtoC ((1 / 4)))  ;  (RtoC (-(1/4))) ] ; [   (RtoC (-(1/4))) ; (RtoC ((1 / 4))) ;  (RtoC (-(1/4)));  (RtoC (1 / 4)) ] ] ) ).
  3: symmetry; apply prob_matrix_0_2.
  3: replace ((⟦ small_grover_total (fs [0%nat; 3%nat]) ⟧) (I 1)) with (list2D_to_matrix ( [ [  (RtoC (1 / 4)) ; (RtoC (-(1/4))) ;(RtoC (-(1/4))) ;  (RtoC (1 / 4))  ] ; [ (RtoC (-(1/4))) ; (RtoC (1 / 4)) ;  (RtoC (1 / 4)) ; (RtoC (-(1/4))) ]  ; [ (RtoC (-(1/4))) ; (RtoC (1 / 4)) ; (RtoC (1 / 4))  ; (RtoC (-(1/4))) ] ; [  (RtoC (1 / 4))  ;(RtoC (-(1/4))) ; (RtoC (-(1/4))) ;  (RtoC (1 / 4)) ] ] ) ).
  4: symmetry; apply prob_matrix_0_3.
  4: replace ((⟦ small_grover_total (fs [1%nat; 2%nat]) ⟧) (I 1)) with (list2D_to_matrix ( [ [  (RtoC (1 / 4)) ;  (RtoC (-(1/4))) ;  (RtoC (-(1 / 4))) ;   (RtoC ((1/4))) ] ; [   (RtoC (-(1/4)));  (RtoC (1 / 4))  ;  (RtoC ((1/4))) ; (RtoC (-(1 / 4)))  ]  ; [ (RtoC (-(1 / 4)))  ;  (RtoC ((1/4))) ; (RtoC ((1 / 4)))  ;  (RtoC (-(1/4))) ] ; [   (RtoC ((1/4))) ; (RtoC (-(1 / 4))) ;  (RtoC (-(1/4)));  (RtoC (1 / 4)) ] ] ) ).
  5: symmetry; apply prob_matrix_1_2.
  5: replace ((⟦ small_grover_total (fs [1%nat; 3%nat]) ⟧) (I 1)) with (list2D_to_matrix ( [ [  (RtoC (1 / 4)) ; (RtoC (-(1/4))) ;(RtoC ((1/4))) ;  (RtoC (-(1 / 4))) ] ; [ (RtoC (-(1/4))) ; (RtoC (1 / 4)) ;  (RtoC (-(1 / 4))) ; (RtoC ((1/4))) ]  ; [ (RtoC ((1/4))) ; (RtoC (-(1 / 4))) ; (RtoC (1 / 4))  ; (RtoC (-(1/4))) ] ; [  (RtoC (-(1 / 4))) ; (RtoC ((1/4))) ; (RtoC (-(1/4))) ;  (RtoC (1 / 4)) ] ] ) ).
  6: symmetry; apply prob_matrix_1_3.
  6: replace ((⟦ small_grover_total (fs [2%nat; 3%nat]) ⟧) (I 1)) with (list2D_to_matrix ( [ [  (RtoC (1 / 4)) ;  (RtoC ((1/4))) ;  (RtoC (-(1 / 4))) ;   (RtoC (-(1/4))) ] ; [   (RtoC ((1/4)));  (RtoC (1 / 4))  ;  (RtoC (-(1/4))) ; (RtoC (-(1 / 4)))  ]  ; [ (RtoC (-(1 / 4)))  ;  (RtoC (-(1/4))) ; (RtoC ((1 / 4)))  ;  (RtoC ((1/4))) ] ; [   (RtoC (-(1/4))) ; (RtoC (-(1 / 4))) ;  (RtoC ((1/4)));  (RtoC (1 / 4)) ] ] ) ).
  7: symmetry; apply prob_matrix_2_3.
  1,2,3,4,5,6 :  unfold Rsum, sum_f_R0;
  unfold count;
  simpl;
  replace (1+1+1)%R with 3%R by ring;
  replace (1+1)%R with 2%R by ring;
  rewrite sqrt_div;
  intuition.
  1,2,3,4,5,6: rewrite asin24.
  1,2,3,4,5,6: replace (2 * 1 + 1)%R with 3%R by R_field.
  1,2,3,4,5,6: rewrite sin_3PI4;
               rewrite Rmult_1_r; unfold Rdiv.
  1,2,3,4,5,6: repeat rewrite Rmult_1_l.
  1,2,3,4,5,6: unfold exp_val_meas_matrix, fst, trace.
  1,2,3,4,5,6: solve_matrix.
  1,2,3,4,5,6: replace  (/ √ 2 * / √ 2)%R with (/ (√ 2 * √ 2))%R.
  2,4,6,8,10,12 : apply Rinv_mult_distr.
  all: try apply sqrt2_neq_0.
  1,2,3,4,5,6: replace (√ 2 * √ 2)%R with  2%R.
  2,4,6,8,10,12 : symmetry; apply sqrt_sqrt.
  all: try intuition.
  1,2,3,4,5,6: R_field_simplify; reflexivity.
  (* unfortunately, rewrite does not find the relevant section in the subgoal to do the below automatically, even though that is why the lemmas are reversed in this file *)
  1: replace ((⟦ small_grover_total (fs [0%nat; 1%nat; 2%nat]) ⟧) (I 1)) with (list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C1 ] ])).
  2: symmetry; apply prob_matrix_0_1_2.
  2: replace ((⟦ small_grover_total (fs [0%nat; 1%nat; 3%nat]) ⟧) (I 1)) with (list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0; C0 ; C0 ]  ; [ C0 ; C0 ; C1 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ])).
  3: symmetry; apply prob_matrix_0_1_3.
  3: replace ((⟦ small_grover_total (fs [0%nat; 2%nat; 3%nat]) ⟧) (I 1)) with (list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C1; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ])).
  4: symmetry; apply prob_matrix_0_2_3.
  4: replace ((⟦ small_grover_total (fs [1%nat; 2%nat; 3%nat]) ⟧) (I 1)) with (list2D_to_matrix ( [ [ C1 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ])).
  5: symmetry; apply prob_matrix_1_2_3.
  Local Close Scope circ_scope.
  Local Open Scope R_scope.
  1,2,3,4: three_true_solution_prep.
  2,4,6,8: unfold Rdiv; rewrite Rmult_comm;
           rewrite Rmult_assoc;
           replace (/ 3 * 3) with (3 * / 3).
  2,4,6,8: replace (3 * / 3) with 1.
  2,4,6,8: rewrite Rmult_1_r; reflexivity.
  2,3,4,5: rewrite Rinv_r.
  2,4,6,8: reflexivity.
  2,3,4,5: easy.
  2,3,4,5: rewrite Rmult_comm.
  2,3,4,5: reflexivity.
  1,2,3,4: replace ((2 * 1 + 1) * (PI / 3))%R
           with PI%R by R_field.
  1,2,3,4: three_true_solution_end.
 Qed.
 
(* unfortunately, separate goals had to be created, because coq would not recognize a rewrite nor would it allow replace with by, both above and below *)
(* since the below result in separate goals in a way that an Ltac cannot handle together, a separate tactic is without point. *)

(* There used to be involutoriness proofs for the circuits themselves 
Lemma involutory_small_oracle_0_2 : forall (s: Square 4), WF_Matrix s -> denote (small_oracle_0_2) ((denote (small_oracle_0_2)) s) = denote (@id_circ  ( Qubit ⊗ Qubit ) ) s.
Proof.
  intros.
  matrix_denote.
  solve_matrix.
Qed.
 

Lemma involutory_small_oracle_1_3 : forall (s: Square 4), WF_Matrix s -> denote (small_oracle_1_3) ((denote (small_oracle_1_3)) s) = denote (@id_circ  ( Qubit ⊗ Qubit ) ) s.
Proof.
  intros.
  matrix_denote.
  solve_matrix.
Qed.




*)
