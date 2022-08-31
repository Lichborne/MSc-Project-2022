Require Import Oracles.
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
Require Import Symmetric.
Require Import Numbers.Natural.Abstract.NDiv.

Local Open Scope circ_scope.


Section Grover.
Open Scope circ_scope.
(* The module structure is based on the SQIR implementation; we posit that
 a given circuitry acting on the relevant matrix representing state implements 
 a given function f : {0,1}^n [represented as nat] -> {0,1}, whatever it may be,
 so we may reason about the circuitry in general. *)


Definition nat_to_var (n : nat) : Var := n. 
Coercion b_var : Var >-> bexp.
Coercion nat_to_var : nat >-> Var.

Variable f: bexp.

Variable m: nat.  Definition k := 2*m-1.

Definition qubit_list : Ctx := repeat (Some Qubit) k.

Lemma den_list_size: denote qubit_list = k.
Proof. unfold qubit_list. induction k. reflexivity.
       simpl. simpl in IHn. rewrite IHn. reflexivity. Qed.

Lemma take_to_type: forall (b: Square_Box S (⟦ qubit_list ⟧) ⨂ Qubit), Square_Box S k ⨂ Qubit.
Proof. rewrite den_list_size. intros. apply b. Qed.
         
Definition grover_oracle :  Box ( S k ⨂ Qubit) ( S k ⨂ Qubit)  := take_to_type (compile f qubit_list).

(* Input expected to be, for m useful qubits, Box ((m*2) ⊗ Qubit) ((m*2) ⊗ Qubit) such that the last m qubtis are ancillae; which is exactly what the oracle will produce. (m/2-1)(indexed from 0) is our target qubits since we have an expanded statespace but want the relevnt qubit n0 should be n/2-2 to start with, but since it is  used to guid the recursin this is only encapulated in the entire definition*)

Fixpoint gen_tof_right {n} n0  (pf: exists m:nat, n/2 = m) :  Box (n ⨂ Qubit) (n ⨂ Qubit) :=
  match n0 with
  | 0 | S 0 =>  box_ qs ⇒
              let_ qs ← Toffoli_at n ((n/2)-2) (n-4) (n-3) $ qs;
              qs

  | S n0'  => box_ qs ⇒
               let_ qs  ← gen_tof_right n0' pf $ qs;
               let_ qs  ← Toffoli_at n (n-(n0+3)) ((n/2)-(n0+1)) (n-(n0+2)) $ qs;
               qs   
  end.

Lemma gen_tof_right_WT: forall n0 pf, Typed_Box (@gen_tof_right m n0 pf).
Proof.
  intros.
  induction n0 as [| [| n0 ] ]; type_check. unfold unbox. apply Toffoli_at_WT. type_check.
  unfold unbox. type_check. apply Toffoli_at_WT. type_check.
Qed.

(* Input expected to be, for m useful qubits, Box ((m*2) ⊗ Qubit) ((m*2) ⊗ Qubit) such that the last m qubtis are ancillae; which is exactly what the oracle will produce*)
Fixpoint gen_tof_left {n} n0 (pf: exists m:nat, n/2 = m) :  Box (n ⨂ Qubit) (n ⨂ Qubit) :=
  match n0 with
  | 0 | S 0 =>  box_ qs ⇒
              let_ qs ← Toffoli_at n 0 1 (n/2)$ qs;
              qs

  | S n0'  => box_ qs ⇒
               let_ qs  ← gen_tof_left n0' pf $ qs;
               let_ qs  ← Toffoli_at n n0 ((n/2)+(n0'-1)) ((n/2)+n0') $ qs;
               qs   
end.

Lemma gen_tof_left_WT: forall n0 pf, Typed_Box (@gen_tof_left m n0 pf).
Proof.
  intros.
  induction n0 as [| [| n0 ] ]; type_check. unfold unbox. apply Toffoli_at_WT. type_check.
  unfold unbox. type_check. apply Toffoli_at_WT. type_check.
Qed.

Lemma div_2_ex: forall (a:nat) (b:nat), a/2 = b -> exists m, a/2 = m.
Proof. intros. apply ex_intro with (x:= b). apply H. Qed.

Lemma div_eq: forall k:nat, k/ 2 = k/2. Proof. intros. reflexivity. Qed.

(*using the above, we can define this in general*)
Definition gen_tof {n} (pf: n >= 6) : Box (n ⨂ Qubit) (n ⨂ Qubit) :=
  match n with
  | 0 | S 0  => id_circ
  | S n0'  => box_ qs ⇒
               let_ qs  ← gen_tof_left (n/2-2) (div_2_ex n (n/2) (div_eq n)) $ qs;
               let_ qs  ← CNOT_at n (n/2) ((n/2)-1) $ qs;
               let_ qs  ← gen_tof_right (n/2-3) (div_2_ex n (n/2) (div_eq n)) $ qs;
               let_ qs ← Toffoli_at n 0 1 (n/2) $ qs;
               qs                                    
end.
(* Variable ρ: Density 32. Definition t := 8.  Lemma gr6: t >= 6. Proof. autounfold. intuition. Qed.
Lemma gentofcor: denote_box true (@gen_tof 8 gr6) ρ = super ( (I 8)) ρ.
Proof. matrix_denote. autounfold with den_db. unfold hoas_to_db_box. unfold denote_db_box. destruct gen_tof. solve_matrix.*)

(*unfinished;
Lemma gen_tof_WT: forall n pf, Typed_Box (@gen_tof n pf).
 Proof.
   intros. unfold gen_tof.
   induction n as [| [| n ] ]. 1,2: type_check.
   unfold Typed_Box. intros.
   unfold unbox. 
Qed. *)
  
Lemma n_smaller_Sn : forall n,
    n < S n.
Proof. intuition. Qed.

Lemma Sn_g_zero : forall n n0 (pf1: S n0 > 0) (pf2: n = S n0),
    n > 0.
Proof. intuition. Qed.

Lemma n_min_smaller_n : forall n,
    n > 0 -> n - 1 < n.
Proof. intuition. Qed.

Lemma nat_trans : forall (n:nat) (m:nat) (k:nat) (pf1: n < m) (pf2: m < k),
    n < k.
Proof. intuition. Qed.

(*Proof. intuition. destruct n0. all: try reflexivity. intuition. Qed.*)

Lemma m_m_zero : forall n0,
    match n0 with
    | 0  => n0 = 0
    | p => p = n0
    end.
Proof. intuition. destruct n0. all:try reflexivity.  Qed.

Lemma subst : forall (a : nat -> Set) (n:nat) (k:nat) (pf: n = k) (an: a k),
      a n.
Proof. intuition. rewrite pf. apply an. Qed.

Fixpoint recursor_n {A:Set} (a:A) (g:A->A) (n:nat) : A :=
  match n with
  | 0 => a
  | S n' => g (recursor_n a g n')
  end.

Lemma sym : forall {A:Set} {a:A} {b:A} (ex : a = b),
    (b = a).
Proof.
intros.  
symmetry.  
apply ex.
Qed.

Fixpoint all_X {n} n0 (pf: n0 < n) :  Box (n ⨂ Qubit) (n ⨂ Qubit) :=
  (match n0 as a return (n0 = a -> _ ) with
  | 0 => fun H : n0 = 0 => X_at n n0 pf
  | S n0' => fun H : n0 = S n0' =>
     (box_ qs ⇒
      let_ qs ← all_X n0' (nat_trans n0' (S n0') n (n_smaller_Sn n0') (subst (fun a => a < n) (S n0') n0 (sym H) pf)) $ qs;
      let_ qs ← X_at n n0 pf $ qs;
      (qs))
   end)
    (eq_refl n0).


Fixpoint all_H {n} n0 (pf: n0 < n) :  Box (n ⨂ Qubit) (n ⨂ Qubit) :=
  (match n0 as a return (n0 = a -> _ ) with
  | 0 => fun H : n0 = 0 => unitary_at1 n _H n0 pf
  | S n0' => fun H : n0 = S n0' =>
     (box_ qs ⇒
      let_ qs ← all_H n0' (nat_trans n0' (S n0') n (n_smaller_Sn n0') (subst (fun a => a < n) (S n0') n0 (sym H) pf)) $ qs;
      let_ qs ← unitary_at1 n _H n0 pf $ qs;
      (qs))
   end)
    (eq_refl n0).

(* This is proven by intuition. apply Numbers.Natural.Abstract.Ndiv.div_lt. all:intuition. Unfortunately, Ndiv stopped being imported even though it is required and accepted, and there has not been time to fix this *)
Fact half_n_minus_smaller_n : forall n:nat,
    n > 0 -> n/2 - 1 < n.
Proof. intros. Admitted.

Lemma if_g6_g0: forall{x} (pf: x >= 6),  x > 0. Proof. intros. intuition. Qed.
(* the diffusion operator proper *)
Definition diffusion_op {n} (pf:n>=6) : Box (n ⨂ Qubit) (n ⨂ Qubit) :=
  box_ qs  ⇒
    let_ qs ← all_H (n/2-1) (half_n_minus_smaller_n n (if_g6_g0 pf)) $ qs;
    let_ qs ← all_X (n/2-1) (half_n_minus_smaller_n n (if_g6_g0 pf)) $ qs;
    let_ qs ← unitary_at1 n _H (n/2-1) (half_n_minus_smaller_n n (if_g6_g0 pf)) $ qs;
    let_ qs ← gen_tof pf $ qs;
    let_ qs ← unitary_at1 n _H (n/2-1) (half_n_minus_smaller_n n (if_g6_g0 pf)) $ qs;
    let_ qs ← all_X (n/2-1) (half_n_minus_smaller_n n (if_g6_g0 pf)) $ qs;
    let_ qs ← all_H (n/2-1) (half_n_minus_smaller_n n (if_g6_g0 pf)) $ qs;
    qs.

Lemma eq_succ_wtype_corr: forall{n k}  (p1: Pat (n ⨂ Qubit)), S k = n -> Pat (S k ⨂ Qubit).
Proof. intros. rewrite H. apply p1. Qed.

Lemma eq_dep_gen: forall{B} (A: B -> Type) (n0:B) (k0:B) (p1: A n0), (n0 = k0)%nat -> A k0.
Proof. intros. symmetry in H. rewrite H. apply p1. Qed.

Lemma eq_succ_wtype_corr_rev: forall{n k}  (p1: Pat (S k ⨂ Qubit)), S k = n -> Pat (n ⨂ Qubit).
Proof. intros. symmetry in H. rewrite H. apply p1. Qed.

(* again, it must be on at least 1 qubit *)
Fixpoint grover_iterations_r {n} (r:nat) (pf: n>=6) (fact_pf: S k = n) : Box (n ⨂ Qubit) (n ⨂ Qubit) :=
  match r with
  | 0 =>  id_circ
  | S r' =>  box_ qs  ⇒
                 let_ qs ← grover_iterations_r r' pf fact_pf $ qs;
                 let_ qs ← grover_oracle $ (eq_succ_wtype_corr qs fact_pf);
                 let_ qs ← diffusion_op (pf) $ (eq_succ_wtype_corr_rev qs fact_pf);
                 qs
end.


Definition grover_algorithm {n} (r:nat) (pf: n>=6) (fact_pf: S k = n) : Box One (n ⨂ Qubit) :=
  box_ ()  ⇒    let_ qs ← initMany false n $ ();
                 let_ qs ← unitary_at1 n _H (n-1) (n_min_smaller_n n (if_g6_g0 pf)) $ qs;
                 let_ qs ← unitary_at1 n _Z (n-1) (n_min_smaller_n n (if_g6_g0 pf)) $ qs;
                 let_ qs ← all_H (n/2-1) (half_n_minus_smaller_n n (if_g6_g0 pf)) $ qs;
                 let_ qs ← grover_iterations_r r pf fact_pf $ qs;
                 qs.

End Grover.
(* The below is in preparation for a potential proof that there was no time to get to evn try------------------------------- *)
(* for any f : nat -> bool, U implements the circuitry that applies that oracle to the density matrix over which it operates *)
Definition padded_boolean_oracle_box {dim} m
  (U : Box (dim ⨂ Qubit) (dim ⨂ Qubit)) (f : nat -> bool) :=
  forall x (y : bool),
  (x < 2 ^ m)%nat ->
      (denote U)
      (@pad (m-2) m dim (outer_product (basis_vector (2 ^ m) x ⊗ (bool_to_ket  y)  ) (basis_vector (2 ^ m) x ⊗  (bool_to_ket  y) )))%M =
    @pad (m-2) m dim (outer_product (basis_vector (2 ^ m) x ⊗ (bool_to_ket (xorb y (f x)))) (basis_vector (2 ^ m) x ⊗ (bool_to_ket (xorb y (f x) ))))%M.
