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


Local Coercion Nat.b2n : bool >-> nat.  

Local Open Scope nat_scope.

(* Classical oracle function. *)
Variable f : nat -> bool.

(* in our limited case of k = 1, we can index the relevant subset of f-s by the x with which they return true *)
Definition f_unique (x:nat) : nat -> bool :=
  (fun y => x =? y).

Lemma f_unique_correct : forall x y, x <> y -> (f_unique x) x = true /\ (f_unique x) y = false.
Proof.
  intros.
  split.
  unfold f_unique.
  symmetry.
  apply beq_nat_refl.
  unfold f_unique.
  apply Nat.eqb_neq.
  apply H.
Qed.

(* type for the four functions for a database of 4 that only return true for one of them,
to delineate scope of current grover's implementation *)
Inductive Unique_Function: (nat -> bool) -> Set :=
    | f0 : Unique_Function (f_unique 0)
    | f1 : Unique_Function (f_unique 1)
    | f2 : Unique_Function (f_unique 2)
    | f3 : Unique_Function (f_unique 3).

(* To illustrate a more usual, but in this case not very nice way of restricting the scope via dependency *)
Inductive Longer_dep_ufunc (x:nat) (pf: x < 4) : (nat->bool) -> Set :=
    | long0 :  x = 0 -> Longer_dep_ufunc x pf (f_unique x)
    | long1 :  x = 1 -> Longer_dep_ufunc x pf (f_unique x)
    | long2 :  x = 2 -> Longer_dep_ufunc x pf (f_unique x)
    | long3 :  x = 3 -> Longer_dep_ufunc x pf (f_unique x).

(*Demonstratively, one-;line version*)
Inductive Short_Ufunc (x:nat) (pf: x < 4) : (nat -> bool) -> Set := one_line :  Short_Ufunc x pf (f_unique x).

(* Demonstratively, general version *)
Inductive U_Func_Ind : (nat -> bool) -> Set :=
    | finductive : U_Func_Ind (f_unique 0%nat)
    | SF :  forall (x:nat), U_Func_Ind (f_unique x) -> U_Func_Ind (f_unique (S x)).

(* Demonstratively, general without full induction *)
Inductive U_Func_Gen :  (nat -> bool ) -> Set := fx : forall (x:nat), U_Func_Gen (f_unique x).
 
(* Variable a in unique func *)
Variable a : nat.

(* limited classical  oracle function *)
Variable (g: Unique_Function (f_unique a)).

(* S gate is derived from the The "controlled phase gate" _R_ m with m = 2, so the rotation = Pi/2*)
Definition _S := _R_ (PI/2).


 (*Tactic for solving Complex Conjegate equivalences below*)
Ltac C1_conjunctive_solve :=
  C_field_simplify;
  try rewrite Copp_involutive;
  unfold C1;
  unfold Cconj;
  try unfold Copp;
  unfold fst, snd;
  try rewrite Ropp_involutive;
  try repeat rewrite Ropp_0;
  reflexivity.

Local Open Scope C_scope.

(* Proof that proving Mmult M M is sufficient for M=M to prove Minv M M *)
Lemma mmult_self_then_minv : forall {m} (M: Square m),
    Mmult M M = I m -> Minv M M.
Proof.
  intros.
  unfold Minv.
  split.
  apply H.
  apply H.
Qed.


(* Proof of involutoriness, sufficient given the above *)
Lemma all_oracles_denoted_matrix_involutory: forall i j k l, i =  C1 \/ i = (-C1) ->  j =  C1 \/ j = (-C1) ->  k =  C1 \/ k = (-C1) ->  l =  C1 \/ l = (-C1) -> Mmult (list2D_to_matrix ( [ [ i ; C0 ; C0 ; C0 ] ; [ C0 ; j; C0; C0 ] ; [ C0 ; C0 ;  k ;C0 ] ; [C0 ; C0; C0 ; l] ] )) (list2D_to_matrix  ( [ [ i ; C0 ; C0 ; C0 ] ; [ C0 ; j; C0; C0 ] ; [ C0 ; C0 ;  k ;C0 ] ; [C0 ; C0; C0 ; l] ] )) = I 4.
Proof.
  intros.
  solve_matrix.
  destruct H. 3: destruct H0. 5: destruct H1. 7: destruct H2.
  1,2: rewrite H. 3,4: rewrite H0. 5,6: rewrite H1. 7,8: rewrite H2.
  all: C_field. 
Qed.


(*Proof that the underlying operators are unitary for all oracles here considered*)
Lemma all_oracles_denoted_matrix_hermitian: forall i j k l, i =  C1 \/ i = (-C1) ->  j =  C1 \/ j = (-C1) ->  k =  C1 \/ k = (-C1) ->  l =  C1 \/ l = (-C1) -> (list2D_to_matrix ( [ [ i ; C0 ; C0 ; C0 ] ; [ C0 ; j; C0; C0 ] ; [ C0 ; C0 ;  k ;C0 ] ; [C0 ; C0; C0 ; l] ] )) = (adjoint (list2D_to_matrix  ( [ [ i ; C0 ; C0 ; C0 ] ; [ C0 ; j; C0; C0 ] ; [ C0 ; C0 ;  k ;C0 ] ; [C0 ; C0; C0 ; l] ] ))).
Proof.
  intros.
  solve_matrix.
  destruct H. 3: destruct H0. 5: destruct H1. 7: destruct H2.
  1,2: rewrite H. 3,4: rewrite H0. 5,6: rewrite H1. 7,8: rewrite H2.
  all: C1_conjunctive_solve. 
Qed.

(* Given that it is sufficient to prove the lemmas as set out below to prove unitarity when a matrix is its own inverse, 
so that we can substitute in itself for its inverse in the proof *)
Lemma inverse_equiv_unit : forall {m} (M1 M2 : Square m),
    M1 = M2 -> Mmult M1 (adjoint M1) = Mmult M2 (adjoint M1).
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

(* Proof of the unitarity of underlying opertors, directly*)
Lemma all_oracles_denoted_matrix_unitary: forall i j k l, i =  C1 \/ i = (-C1) ->  j =  C1 \/ j = (-C1) ->  k =  C1 \/ k = (-C1) ->  l =  C1 \/ l = (-C1) -> (Mmult (list2D_to_matrix ( [ [ i ; C0 ; C0 ; C0 ] ; [ C0 ; j; C0; C0 ] ; [ C0 ; C0 ;  k ;C0 ] ; [C0 ; C0; C0 ; l] ] )) (adjoint (list2D_to_matrix  ( [ [ i ; C0 ; C0 ; C0 ] ; [ C0 ; j; C0; C0 ] ; [ C0 ; C0 ;  k ;C0 ] ; [C0 ; C0; C0 ; l] ] )))) = I 4.
Proof.
  intros.
  solve_matrix.
  destruct H. 3: destruct H0. 5: destruct H1. 7: destruct H2.
  1,2: rewrite H. 3,4: rewrite H0. 5,6: rewrite H1. 7,8: rewrite H2.
  all: C1_conjunctive_solve. 
 Qed.

(* equality is a congruence on A - by definition, of course*)
Lemma cong_eq : forall (A:Type) (a:A) (b:A) (f : A -> A), a = b -> f a = f b.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

(* equality is a congruence on A in f with f equal to partial application f a below*)
Lemma cong_eq_in_f_partial : forall (A:Type) (a:A) (b:A) (c:A) (f: A -> A), f a = c -> a = b -> f b = c.
Proof.
  intros.
  apply (cong_eq A a0 b f4)  in H0.
  symmetry in H0. rewrite H0.
  apply H.
Qed.

(* equality is a congruence on A in f *)
Lemma cong_eq_in_f : forall (A:Type) (a:A) (b:A) (c:A) (f: A -> A -> A), f a a = c -> a = b -> f a b = c.
Proof.
  intros.
  rewrite (cong_eq_in_f_partial A a0 b c (f4 a0)).
  symmetry in H.
  split.
  apply H.
  apply H0.
Qed. 

(* Given the above, we can prove unitarity in a different way: *)
Lemma involutory_and_hermitian_then_unitary : forall (m:nat) (M: Square m),
    Mmult M M = I m -> M = adjoint M -> Mmult M (adjoint M) = I m.
Proof. 
  intros.
  apply cong_eq_in_f.
  apply H.
  apply H0.
Qed.

(*multiplication is commutative on these*)
Lemma oracles_denoted_matrix_mult_comm : forall i j k l m n o p, (i =  C1 \/ i = (-C1)) ->  j =  C1 \/ j = (-C1) ->  k =  C1 \/ k = (-C1) ->  l =  C1 \/ l = (-C1) ->  m = C1 \/ m = (-C1) ->  n =  C1 \/ n = (-C1) ->  p =  C1 \/ p = (-C1) ->  o =  C1 \/ o = (-C1) -> Mmult (list2D_to_matrix ( [ [ i ; C0 ; C0 ; C0 ] ; [ C0 ; j; C0; C0 ] ; [ C0 ; C0 ;  k ;C0 ] ; [C0 ; C0; C0 ; l] ] )) (list2D_to_matrix  ( [ [ m ; C0 ; C0 ; C0 ] ; [ C0 ; n; C0; C0 ] ; [ C0 ; C0 ;  o ;C0 ] ; [C0 ; C0; C0 ; p] ] )) = Mmult  (list2D_to_matrix  ( [ [ m ; C0 ; C0 ; C0 ] ; [ C0 ; n; C0; C0 ] ; [ C0 ; C0 ;  o ;C0 ] ; [C0 ; C0; C0 ; p] ] )) (list2D_to_matrix  ( [ [ i ; C0 ; C0 ; C0 ] ; [ C0 ; j; C0; C0 ] ; [ C0 ; C0 ;  k ;C0 ] ; [C0 ; C0; C0 ; l] ] )).
Proof.
  intros.
  solve_matrix.
Qed.
  
Local Close Scope nat_scope.
Local Open Scope circ_scope.

(* Oracle for f(0) = true, else false *) 
 Definition small_oracle_0 : Box ( Qubit ⊗ Qubit ) ( Qubit ⊗ Qubit ) :=
   box_ (x, y) ⇒
     let_ x ← _Z $ x;
     let_ y ← _Z $ y;
     let_ (x,y) ← ctrl _Z $ (x,y);
     (x,y).

(*well-typedness lemma for small_oracle_0; same for oracles below*)
Lemma small_oracle_0_WT : Typed_Box (small_oracle_0).
Proof. type_check. Qed.

(* Correctness lemma for small_oracle_0; same for oracles below *)
Lemma correct_small_oracle_0 : forall (s: Square 4), WF_Matrix s -> denote (small_oracle_0) s = super (list2D_to_matrix ( [ [ (-C1) ; C0 ; C0 ; C0 ] ; [ C0 ; C1; C0; C0 ] ; [ C0 ; C0 ; C1 ;C0 ] ; [C0 ; C0; C0 ; C1] ] )) s.
 Proof.
   matrix_denote.
   solve_matrix.
 Qed.

 (* Oracle for f(1) = true, else false *) 
Definition small_oracle_1 :
Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
 box_ (x, y) ⇒
   let_ y ← _Z $ y;
   let_ (x,y) ← ctrl _Z $ (x,y);
   (x,y).

Lemma small_oracle_1_WT : Typed_Box (small_oracle_1).
Proof. type_check. Qed.

Lemma correct_small_oracle_1 : forall (s: Square 4), WF_Matrix s -> denote (small_oracle_1) s = super (list2D_to_matrix ( [ [ C1 ; C0 ; C0 ; C0 ] ; [ C0 ; (-C1); C0; C0 ] ; [ C0 ; C0 ; C1 ;C0 ] ; [C0 ; C0; C0 ; C1] ] )) s.
Proof.
   matrix_denote.
   solve_matrix.
Qed.

(* Oracle for f(2) = true, else false *) 
 Definition small_oracle_2:
 Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  box_ (x, y) ⇒
    let_ x ← _Z $ x;
    let_ (x,y) ← ctrl _Z $ (x,y);
    (x,y).

Lemma small_oracle_2_WT : Typed_Box (small_oracle_2).
Proof. type_check. Qed.

 Lemma correct_small_oracle_2 : forall (s: Square 4), WF_Matrix s -> denote (small_oracle_2) s = super (list2D_to_matrix ( [ [ C1 ; C0 ; C0 ; C0 ] ; [ C0 ; C1; C0; C0 ] ; [ C0 ; C0 ; (-C1) ;C0 ] ; [C0 ; C0; C0 ; C1] ] )) s.
 Proof.
   matrix_denote.
   solve_matrix.
 Qed.
 
(* Oracle for f(3) = true, else false *) 
 Definition small_oracle_3 :
 Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  box_ (x, y) ⇒
    let_ (x,y) ← ctrl _Z $ (x,y);
    (x,y).

Lemma small_oracle_3_WT : Typed_Box (small_oracle_3).
Proof. type_check. Qed.

Lemma correct_small_oracle_3 : forall (s: Square 4), WF_Matrix s -> denote (small_oracle_3) s = super (list2D_to_matrix ( [ [ C1 ; C0 ; C0 ; C0 ] ; [ C0 ; C1; C0; C0 ] ; [ C0 ; C0 ; C1 ;C0 ] ; [C0 ; C0; C0 ; (-C1)] ] )) s.
Proof.
   matrix_denote.
   solve_matrix.
Qed.

(* diffusion operator for 2 qubits *)
Definition small_diffusion : Box ( Qubit ⊗ Qubit ) ( Qubit ⊗ Qubit ) :=
  box_ (x, y) ⇒
    (*step 1*)
    let_ x ← _H $ x;
    let_ y ← _H $ y;
    (*step 2*)
    let_ x ← _X $ x;
    let_ y ← _X $ y;
    (*step 3*) 
    let_ (x,y) ← ctrl _Z $ (x,y);
    (*step 4*)
    let_ x ← _X $ x;
    let_ y ← _X $ y;
    (*step 5*)
    let_ x ← _H $ x;
    let_ y ← _H $ y;
    (*end*)
    (x,y).

(* well-typedness lemma *)
Lemma small_diffusion_WT : Typed_Box (small_diffusion).
Proof. type_check. Qed.


(* First part of tactic proving that certain Real values are nonzero (this is a bit finnicky because reals are axiomatic in coq) 
   Need for separation explained below *)
Ltac grover_nonzero_begin :=
  unfold C2;
  apply C0_fst_neq;
  unfold fst;
  replace 2%R with (sqrt 2 * sqrt 2)%R.

(* Second part of tactic for proving that certain Real values are nonzero *)
Ltac grover_nonzero_end :=
  apply Rmult_integral_contrapositive;
  split;
  apply sqrt2_neq_0;
  apply sqrt2_neq_0;
  apply sqrt_sqrt;
  intuition.

(* matrix form to help verify correctness; it is established, but commented out for now because it takes too long to run. Uncomment if desired*)
Definition diffusion_matrix : Square 4 := (list2D_to_matrix ( [ [ (-(1/2)); (1/2) ; (1/2) ; (1/2) ] ; [ (1/2) ; (-(1/2)) ;(1/2); (1/2)]  ; [ (1/2) ; (1/2) ; (-(1/2)) ; (1/2) ] ; [ (1/2) ; (1/2) ; (1/2) ; (-(1/2)) ] ] )).

(* The below runs perfectly fine, but way too slowly, so it is commented out *)
(*Lemma correct_small_diffusion : forall (s:Square 4), WF_Matrix s -> denote (small_diffusion) s = super diffusion_matrix s.
Proof.                                                                                      unfold diffusion_matrix.
  matrix_denote.
  Msimpl.
  simpl.
  repeat rewrite <- Mmult_assoc.
                                                                          
  replace (I 2 ⊗ hadamard)%M with (list2D_to_matrix ( [ [ (1/ sqrt(2));  (1/ sqrt(2)) ; C0; C0 ] ; [  (1/ sqrt(2)) ; (- (1/ sqrt(2))) ; C0 ; C0]  ; [ C0 ; C0 ;  (1/ sqrt(2));  (1/ sqrt(2))] ; [ C0 ; C0 ;  (1/ sqrt(2));  (-(1/ sqrt(2)))] ] )).
  2: { solve_matrix. }
  replace (hadamard ⊗ I 2)%M with (list2D_to_matrix ( [ [ (1/ sqrt(2));  C0 ;  (1/ sqrt(2)); C0 ] ; [  C0 ;  (1/ sqrt(2)) ; C0 ;  (1/ sqrt(2))]  ; [  (1/ sqrt(2)) ; C0 ;  (-(1/ sqrt(2))); C0] ; [ C0 ; (1/ sqrt(2)) ;  C0;  (-(1/ sqrt(2)))] ] )).
  2: { solve_matrix. }
  replace (adjoint(hadamard) ⊗ I 2)%M with (list2D_to_matrix ( [ [ (1/ sqrt(2));  C0 ;  (1/ sqrt(2)); C0 ] ; [  C0 ;  (1/ sqrt(2)) ; C0 ;  (1/ sqrt(2))]  ; [  (1/ sqrt(2)) ; C0 ;  (-(1/ sqrt(2))); C0] ; [ C0 ; (1/ sqrt(2)) ;  C0;  (-(1/ sqrt(2)))] ] )).
  2: { solve_matrix. }
  solve_matrix.
  all: C_field_simplify. all: replace ((R1 + R1)%R, (R0 + R0)%R)%core with C2.
  all: C_field_simplify.
  all: solve_matrix.
  all: split.
  all: try apply Csqrt2_neq_0.
  all: grover_nonzero_begin.
  all: try apply sqrt_sqrt.
  2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32: intuition.
  all: try grover_nonzero_end.
Qed. *)

(*involutoriness of the diffusion operator *)
Lemma involutory_diffusion: Mmult diffusion_matrix diffusion_matrix = I 4.
Proof. solve_matrix. Qed.

(*and relying on this, its unitarity *)
 Lemma unitary_small_diffusion : diffusion_matrix = adjoint diffusion_matrix.
Proof. unfold diffusion_matrix. solve_matrix. Qed.

(* combining the above, we have the full function *)
Definition small_grover {a} (g : Unique_Function (f_unique a)) :  Box One (Qubit ⊗ Qubit) :=
  box_ () ⇒
    let_ x ← _H $ init0 $ ();
    let_ y ← _H $ init0 $ ();
match g with
  | f0 => 
        (let_ (x,y) ← small_oracle_0 $ (x,y);
        let_ (x,y) ← small_diffusion $ (x,y);
        (x,y))
  | f1 => 
        (let_ (x,y) ← small_oracle_1 $ (x,y);
        let_ (x,y) ← small_diffusion $ (x,y);
        (x,y))
  | f2 => 
        (let_ (x,y) ← small_oracle_2 $ (x,y);
        let_ (x,y) ← small_diffusion $ (x,y);
        (x,y))
  | f3 => 
        (let_ (x,y) ← small_oracle_3 $ (x,y);
        let_ (x,y) ← small_diffusion $ (x,y);
        (x,y))
end.

Lemma small_grover_WT : Typed_Box (small_grover g).
Proof. type_check. destruct g. all: type_check. Qed.


(*probability of measuring ξ on the first m qubits of ρ; we will onlz need actual measurements here but this is such a neat definition for something much more general that it is used instead of a specific case*)
Definition exp_val_meas_matrix {n} ( A: Density (2^n)) (ρ : Density (2^n)) : R :=
  fst (trace (Mmult ρ A)).

(* First part of solution tactic for result of gate composition *)
Ltac grover_2qubit_denote_to_nonzero :=
  matrix_denote;
  solve_matrix;
  repeat rewrite Cexp_PI2;
  solve_matrix;
  C_field_simplify;
  Msimpl;
  simpl;
  solve_matrix;
  split.

(* correctness of a songle iteration for each oracle: ---------------------------------------------*)

Lemma prob_matrix_0 : list2D_to_matrix ( [ [ C1 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] ) = denote (small_grover f0) (I 1).
Proof.
  unfold small_grover.
  unfold compose.
  grover_2qubit_denote_to_nonzero.
  all: C_field.
Qed.

Lemma prob_matrix_1 : list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C1 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] ) = denote (small_grover f1) (I 1).
Proof.
  grover_2qubit_denote_to_nonzero.
  all: C_field.
Qed.


Lemma prob_matrix_2 : list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C1 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] ) = denote (small_grover f2) (I 1).
Proof.
  grover_2qubit_denote_to_nonzero.
  all: C_field.
Qed.

Lemma prob_matrix_3 : list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C1 ] ] ) = denote (small_grover f3) (I 1).
Proof.
  grover_2qubit_denote_to_nonzero.
  all: C_field.
Qed.

(* ------------------------------------------------------------------------------------------------*)

Local Close Scope nat_scope.

Definition get_true_value (g : Unique_Function (f_unique a)) : nat :=
  a.

(* correctness lemma for 2 qubits 1 rotatio *)
Lemma small_grover_correct_prob : forall g : Unique_Function (f_unique a),
  match g with
    | f0 => @exp_val_meas_matrix 2 
    (outer_product (basis_vector (4) 0) (basis_vector (4) 0))
    (denote (small_grover f0) (I 1))
    | f1 => @exp_val_meas_matrix 2 
    (outer_product (basis_vector (4) 1) (basis_vector (4) 1))
    (denote (small_grover f1) (I 1))
    | f2 => @exp_val_meas_matrix 2
    (outer_product (basis_vector (4) 2) (basis_vector (4) 2))
    (denote (small_grover f2) (I 1))
    | f3 => @exp_val_meas_matrix  2
    (outer_product (basis_vector (4) 3) (basis_vector (4) 3))
    (denote (small_grover f3) (I 1))
    end
 
               = 
        (sin ((2 * 1 + 1) * asin (√ (1 / 4))) ^ 2)%R.                        (* k = 1 because there is only ever one solution*) 
                       
Proof.
  intros.
   (* rewrite would not recognize the goals (even with explicit inverted lemmas), so manual is the only way*) 
  1: replace (denote (small_grover f0) (I 1)) with  (list2D_to_matrix ( [ [ C1 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] )).
  2: apply prob_matrix_0.
  1: replace (denote (small_grover f1) (I 1)) with  (list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C1 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] )).
  2: apply prob_matrix_1.
  1: replace (denote (small_grover f2) (I 1)) with  (list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C1 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ] ] )).
  2: apply prob_matrix_2.
  1: replace (denote (small_grover f3) (I 1)) with  (list2D_to_matrix ( [ [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C0 ]  ; [ C0 ; C0 ; C0 ; C0 ] ; [ C0 ; C0 ; C0 ; C1 ] ] )).
  2: apply prob_matrix_3.
  destruct g0.
  all: simpl.
  all: replace (2 * 1 + 1)%R with 3%R by ring;
  rewrite sqrt_div_alt;
  replace (asin (sqrt 1 / sqrt 4))%R with (PI/6)%R.
  all: try rewrite Rmult_1_r.
  all: try intuition.
  all: try symmetry; try apply asin14.
  all:unfold outer_product, basis_vector, exp_val_meas_matrix.
  all:unfold trace, fst.
  all: solve_matrix.
  all: repeat rewrite Rmult_0_l, Rmult_0_r, Rplus_0_l.
  all: repeat rewrite Rmult_1_r.
  all: R_field_simplify.
  all: replace (3 * (PI / 6))%R with (1 * (PI / 2))%R.
  all: try rewrite Rmult_1_l.
  all: try rewrite sin_PI2.
  all: try ring.
  all: unfold Rdiv.
  all: symmetry.
  all: rewrite Rmult_comm.
  all: rewrite Rmult_assoc.
  all: replace (/ 6 * 3)%R with (3 * / 6)%R by ring.
  all: replace (3 * / 6)%R with (/ 2)%R.
  all: R_field_simplify.
  all: reflexivity.
Qed.

(*-------------------------------------------------------------------------------------------*)
(*As an additional bit, we have this: *)
(* The definition and correctness of the bell_11 state *)
  Definition bell_11 : Box One (Qubit ⊗ Qubit) :=
    box_ () ⇒
         let_ x ← init0 $ ();
         let_ y ← init0 $ ();
         let_ x ← _H $ x;
         let_ (x,y) ← CNOT $ (x,y);
         let_ x ← _X $ _Z $ x;
         (x,y).

Definition exp_val_matrix {m n} (ξ : Density (2^m)) (ρ : Density (2^(n+m))) : R :=
  fst (trace (Mmult ξ ρ)).

Lemma bell_11_matrix : (denote bell_11 (I 1)) = (list2D_to_matrix ( [ [C0;C0;C0;C0]  ;[C0; (C1/C2)%C ;(-C1/C2)%C ;C0] ;[C0;(-C1/C2)%C ; (C1/C2)%C ;C0] ;[C0;C0;C0; C0] ])).
  matrix_denote.
  solve_matrix.
Qed.

Lemma bell_11_correct :  @exp_val_matrix  2 2  (list2D_to_matrix ( [ [C1;C0;C0;C0]  ;[C0; C0 ;C0;C0] ;[C0;C0; C0 ;C0] ;[C0;C0;C0; C1] ])) (denote bell_11 (I 1)) = 0%R.
Proof.
  replace (denote bell_11 (I 1))  with (list2D_to_matrix ( [ [C0;C0;C0;C0]  ;[C0; (C1/C2)%C ;(-C1/C2)%C ;C0] ;[C0;(-C1/C2)%C ; (C1/C2)%C ;C0] ;[C0;C0;C0; C0] ])).
  2: symmetry; apply bell_11_matrix.
  solve_matrix.
  unfold exp_val_matrix.
  solve_matrix.
  R_field.
Qed.

(* Other things that have been done, and may serve to be of value, but are not now relevant. Note that some require rescoping *)
(*============================================================================================================================*)
(* (H|0>)^⊗n proof of its invlutoriness remained incomplete so was scrapped

Definition P (p:nat) :  Square p := (fun i j => if i <? p then (if j <? p then C1/(RtoC (INR p)) else C0) else C0).

(*well-formed P*)
Lemma WF_P : forall p:nat,  WF_Matrix (P p).
  intros.
  unfold P.
  unfold WF_Matrix.
  intros.
  destruct H.
  replace (ge x p) with (le p x) in H. 2: intuition.
  1,2: bdestruct ( x <? p). 1,3: bdestruct (y <? p).
  all: intuition.
Qed.*)


(*
Definition equal_superposition : Box One (Qubit ⊗ Qubit) :=
  box_ () ⇒
    let_ x ← _H $ init0 $ ();
    let_ y ← _H $ init0 $ ();
(x,y).

Lemma equa_sup_WT : Typed_Box (equal_superposition).
Proof. type_check. Qed.

Definition small_grover_rots_0 : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
 box_ (x,y) ⇒
              let_ (x,y) ← small_oracle_0 $ (x,y);
              let_ (x,y) ← small_diffusion $ (x,y);
(x,y).
     

Definition small_grover_rots_1 : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
   box_ (x,y) ⇒
          let_ (x,y) ← small_oracle_1 $ (x,y);
          let_ (x,y) ← small_diffusion $ (x,y);
          (x,y).


Definition small_grover_rots_2 : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  box_ (x,y) ⇒
              let_ (x,y) ← small_oracle_2 $ (x,y);
              let_ (x,y) ← small_diffusion $ (x,y);
              (x,y).


Definition small_grover_rots_3 : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  box_ (x,y) ⇒
              let_ (x,y) ← small_oracle_3 $ (x,y);
              let_ (x,y) ← small_diffusion $ (x,y);
(x,y).



Fixpoint grover_iteration_HH {n} (r:nat) (g : Unique_Function (f_unique a)) (ψ: Density n):  Density n  :=
  match r with
  | 0%nat  => ψ
  | S r' => match g with
           | f0 => grover_iteration_HH r' g (denote small_grover_rots_0 ψ)
           | f1 => grover_iteration_HH r' g (denote small_grover_rots_1 ψ)
           | f2 => grover_iteration_HH r' g (denote small_grover_rots_2 ψ)
           | f3 => grover_iteration_HH r' g (denote small_grover_rots_3 ψ)
                                      
           end
              end.
  
Fixpoint small_grover_r_rots_0 : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  match r with
  | 0%nat => id_circ
  | S r' => box_ (x,y) ⇒
             (let_ (x,y) ← small_grover_r_rots_0 r' $ (x,y);
              let_ (x,y) ← small_oracle_0 $ (x,y);
              let_ (x,y) ← small_diffusion $ (x,y);
              (x,y))
  end.

Lemma small_grover_r_rots_0_WT : forall r, Typed_Box (small_grover_r_rots_0 r).
Proof. intros.  induction r as [ | r]; type_check.  Qed.


Fixpoint small_grover_r_rots_1 (r:nat): Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  match r with
  | 0%nat => id_circ
  | S r' => box_ (x,y) ⇒
             (let_ (x,y) ← small_grover_r_rots_1 r' $ (x,y);
              let_ (x,y) ← small_oracle_1 $ (x,y);
              let_ (x,y) ← small_diffusion $ (x,y);
              (x,y))
  end.

Lemma small_grover_r_rots_1_WT : forall r, Typed_Box (small_grover_r_rots_1 r).
Proof. intros.  induction r as [ | r]; type_check.  Qed.


Fixpoint small_grover_r_rots_2 (r:nat): Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  match r with
  | 0%nat => id_circ
  | S r' => box_ (x,y) ⇒
             (let_ (x,y) ← small_grover_r_rots_2 r' $ (x,y);
              let_ (x,y) ← small_oracle_2 $ (x,y);
              let_ (x,y) ← small_diffusion $ (x,y);
              (x,y))
  end.

Lemma small_grover_r_rots_2_WT : forall r, Typed_Box (small_grover_r_rots_2 r).
Proof. intros.  induction r as [ | r]; type_check.  Qed. 


Fixpoint small_grover_r_rots_3 (r:nat): Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  match r with
  | 0%nat => id_circ
  | S r' => box_ (x,y) ⇒
             (let_ (x,y) ← small_grover_r_rots_3 r' $ (x,y);
              let_ (x,y) ← small_oracle_3 $ (x,y);
              let_ (x,y) ← small_diffusion $ (x,y);
              (x,y))
  end.

Lemma small_grover_r_rot_3_WT : forall r, Typed_Box (small_grover_r_rots_3 r).
Proof. intros.  induction r as [ | r]; type_check.  Qed.

Fixpoint small_grover_r_rots (r:nat) : Box One (Qubit ⊗ Qubit) :=
  box_ () ⇒
    let_ (x, y) ← equal_superposition $ ();
    match g with
    | f0 => 
        (let_ (x,y) ← small_grover_r_rots_0 r $ (x,y); 
        (x,y))
    | f1 => 
        (let_ (x,y) ← small_grover_r_rots_1 r $ (x,y); 
        (x,y))
    | f2 => 
        (let_ (x,y) ← small_grover_r_rots_2 r $ (x,y); 
        (x,y))
    | f3 => 
        (let_ (x,y) ← small_grover_r_rots_3 r $ (x,y); 
        (x,y))
end.
*)
