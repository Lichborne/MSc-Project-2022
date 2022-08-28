Require Import DBCircuits.
Require Import TypeChecking.
Require Import Denotation.
Require Import Composition.
Require Import VectorDef.
Require Import Nat.
Require Import List.

(*below functions and proofs are taken from and behaviour, and are verified in QuantumLib. redeclaration required due to notation conflict.

 The INQWIRE Developers. (2022). INQWIRE QuantumLib (Version 1.0.0) [Computer software]. https://github.com/inQWIRE/QuantumLib*)
(*============================================================================*)
Definition bool_to_matrix (b : bool) : Matrix 2 2 := if b then ∣1⟩⟨1∣ else ∣0⟩⟨0∣.

Definition bools_to_matrix (l : list bool) : Square (2^(length l)) := 
  big_kron (map bool_to_matrix l).
(*this is technically new but it's essectially identical to ftovec, only for matrices *)
Fixpoint f_to_matrix (n : nat) (f : nat -> bool) : Square (2^n) :=
  match n with 
  | 0 => I 1
  | S n' => kron (f_to_matrix n' f) (bool_to_matrix (f n'))
  end.

Definition f_to_vec' (n : nat) (f : nat -> C) : Vector n :=
  fun i j => if (j =? 0) && (i <? n) then f i else C0. 

Fixpoint incr_bin (l : list bool) :=
  match l with
  | []        => [true]
  | false :: t => true :: t
  | true :: t  => false :: (incr_bin t)
  end.

Fixpoint nat_to_binlist' n :=
  match n with
  | O    => []
  | S n' => incr_bin (nat_to_binlist' n')
   end.

Fixpoint binlist_to_nat (l : list bool) : nat :=
  match l with
  | [] => 0
  | b :: l' => match b with
             | true => 1%nat + 2*binlist_to_nat l'
             | false => 0%nat + 2*binlist_to_nat l'
             end
  end.

Fixpoint funbool_to_list (len : nat) (f : nat -> bool) :=
  match len with
  | O => []
  | S len' => f len' :: funbool_to_list len' f
  end.

Definition funbool_to_nat (len : nat) (f : nat -> bool) :=
  binlist_to_nat (funbool_to_list len f).

Definition shift {A} (f : nat -> A) (k:nat) := fun i:nat => f (add i k).


(*The "controlled phase gate" 'R_ m is the phase_shift gate with 
   e ^ (2*pi*i / 2^m) in the bottom right *)
Definition RNat (m : nat) := _R_ (2 * PI / INR(2^m)).

(* Authors checked this against Quipper implementation *)
(* This did not want to work in my implementation; tunred out we need this to have n + 2 as the number of qubits due to how Qwire is set up, m = additional argument *)
Fixpoint rotations (n m : nat) {struct n}
                 : Box ((S (S n) ⨂ Qubit)) ((S (S n) ⨂ Qubit)) :=
  match n with
  | 0    => id_circ
  | S n' => match n' with
            | 0 => id_circ
            | S _ => 
               box_ (c,(q,qs)) ⇒
               let_ (c,qs) ← rotations n' m $ (c,qs);
               let_ (c,q)  ← ctrl (RNat (m + 2 - n')) $ (c,q);
               (c,(q,qs))
            end
end.
(*Redone *)
Lemma rotations_WT : forall n m, Typed_Box (rotations n m).
Proof. 
  induction n as [ | [ | n]]; type_check.
   apply IHn. 
  type_check.
Qed.

Definition qft_rotations n := rotations (n-1) n.

(* This is identical to the existing implementation, hence not our work*)
(*-----------------------------------------------------------------------------------*)

Program Fixpoint QFT (n : nat) : Box (n ⨂ Qubit) (n ⨂ Qubit) :=
  match n with 
  | 0    => id_circ
  | S n' => match n' with
           | 0 => box_ (q,u) ⇒ (_H $ q, u)
           | S n'' => box_ (q,qs) ⇒
                        let_ qs     ← QFT n' $ output qs; 
                        let_ (q,qs) ← rotations n'' n' $ (q,qs);
                        (_H $ q,qs)
           end
  end.

Lemma QFT_WT : forall n, Typed_Box  (QFT n).
Proof. induction n as [ | [ | n]]; type_check.
       apply rotations_WT; type_check.
Qed.


(*=====================================================================================*)
(* implementation *)
(*  specific lemmas, because it's a little finnicky locally in the rotations proofs *)
(*-----------------------------------------------------------------------------------*)
Lemma basic : forall (n:nat),
    ((S n) > 0)%nat.
Proof.
  intro n.
  try lia.
Qed.


Delimit Scope R_scope with R.
Local Open Scope R_scope.

Lemma cexp0 : forall (a:R) (b:R) (c:R) (d:R),
    Cexp (a * b * c * 0%R * d) = C1.
Proof.
  intros.
  replace (a * b * c * 0%R * d) with (0%R).
  2: ring.
  apply Cexp_0.
Qed.

Lemma cexp1 :
  Cexp (2 * PI * 1 * 1) = C1.
Proof.
  replace (2 * PI * 1 * 1) with (2 * PI).
  2: ring.
  apply Cexp_2PI.
Qed.

Local Close Scope R_scope.


(*helper for below to be proven*)
Fixpoint enlist (n:nat) : list nat:=
  match n with
  |0 => []
  |S n' => n' ::  (enlist (n'))
  end.

(*BELOW TWO ARE REDUNDANT FOR NOW BECAUSE A NATUTAL TO BINARY BASED REPRESENTATION IS USED IN THE EYPONENT IN ROTATIONS FOR NOW; WILL BE A BETTER PROOF FOR HOAS TO DO IT WITH MATRICES*)

(* This is so because Density n is equal to some vector n (outerproduct) vector n adjoint*)
Definition Den_to_StateVec {n:nat} (ρ: Density n) : Vector n :=
  normalize (fun i j => (if (j =? 0) && (ltb i n) then ρ i 1%nat / ρ n 1%nat else C0)).

Definition drop_and_dot {n} (v :  Vector n):  Vector (n-1) :=
  (v 0%nat 0%nat) .* (fun i j => (if (j =? 0) && (ltb i n) && (ltb 0 i) then v i 0%nat else C0)).

Local Coercion Nat.b2n : bool >-> nat.
Lemma qft_rotations_correct : forall n f,
    (n > 0)%nat ->
    denote (qft_rotations n) (f_to_matrix n f) = 
      Cexp (2 * PI * INR (f 0%nat) * INR (funbool_to_nat (n-1) (shift f 1%nat)) * (Rinv 2^n)) .* (f_to_matrix n f).
Proof. 
  intros n f Hn.
  destruct n; try lia.
  induction n.
  - simpl denote.
    unfold denote_box.
    unfold denote_db_box.
    simpl.
    unfold pad.
    unfold denote_pat.
    unfold swap_list.
    simpl.
     unfold swap_two.
    simpl.
    unfold super.
    replace (2 * 1)%R with 2%R by ring.
    replace (Cexp (2 * PI * INR (f 0%nat) * 0 * (/ 2 * 1))%R) with C1.
    unfold scale.
    unfold Cmult.
    unfold bool_to_matrix.
    simpl.
    solve_matrix.
    replace (2 * PI * INR (f 0)%nat * 0 * (/ 2 * 1))%R with 0%R by R_field.
    symmetry.
    apply Cexp_0.
Abort.
    (* -
    symmetry.
    replace (/ 2 * 1)%R with (/2)%R by ring. 
    apply cexp0.
  -  pose proof basic as b.
     specialize (b n).
     pose proof (IHn b).
     simpl. simpl in H.   
    unfold denote_box, denote_db_box, hoas_to_db_box.
    unfold denote_box in H. unfold denote_db_box in H. unfold hoas_to_db_box in H.
    rewrite add_fresh_split. rewrite add_fresh_split in H.
    simpl. simpl in H.
    unfold funbool_to_nat, shift; simpl.
    unfold outer_product.
    apply rotations_WT.
    destruct (f (S O)); destruct (f O); simpl.
    autorewrite with R_db; reflexivity. 
    unfold denote_db_circuit. unfold denote_db_circuit in H.
    rewrite size_ntensor. rewrite size_ntensor in H.
    simpl. simpl in H.
    unfold add_fresh_pat. unfold add_fresh_pat in IHn.
    auto with wf_db.
    unfold shift. unfold shift in IHn.
    unfold funbool_to_nat. unfold funbool_to_nat in IHn.
    unfold funbool_to_list. unfold funbool_to_list in IHn.
    unfold binlist_to_nat. unfold binlist_to_nat in IHn.
    destruct n.
    all: simpl.
    all: destruct (if f 1 then 1 else 0).
     + simpl.
       replace (/2 * 1)%R with (/2)%R by ring.
       replace (Cexp (2 * PI * INR (f 0%nat) * 0 * (/ 2 * / 2))) with C1.
       2: { symmetry. apply cexp0. }
        unfold pad.
       unfold denote_pat.
       auto with wf_db.
       simpl.
       unfold I.
       unfold super.
       unfold swap_list.
       destruct (f 0), (f 1).
       all: unfold bool_to_ket.
       all: Msimpl. all: simpl. all: unfold outer_product.
       all: solve_matrix.
    +  
       replace (/2 * 1)%R with (/2)%R by ring.
       (* prove S n case *)
       2: { symmetry. apply cexp0. }
        unfold pad.
       unfold denote_pat.
       auto with wf_db.
       simpl.
       unfold I.
       unfold super.
       unfold swap_list.
       destruct (f 0), (f 1).
       all: unfold bool_to_ket.
       all: Msimpl. all: simpl. all: unfold outer_product.
       all: solve_matrix.
       
       all: unfold outer_product.
       all: solve_matrix.
       all: auto with  wf_db.
       unfold swap_list_aux.
       destruct (swap_list 3 [subst_var (add_fresh_state (Qubit ⊗ (Qubit ⊗ (Qubit ⊗ One))) []) 0; subst_var (add_fresh_state (Qubit ⊗ (Qubit ⊗ (Qubit ⊗ One))) []) 1; subst_var (add_fresh_state (Qubit ⊗ (Qubit ⊗ (Qubit ⊗ One))) []) 2]).
        unfold swap_list.
        simpl.
        unfold swap_two.
        simpl.
        unfold super.
        unfold scale.
        unfold Cmult.
        unfold outer_product.
        simpl.
        unfold I.
        destruct (f 1).
        all: destruct (f 0).
        all: simpl.
        all: unfold Mmult.
        all: destruct 8.
        all: solve_matrix.
        solve_matrix.
        unfold super.
      destruct (c (qubit 0,, (qubit 1,, (qubit 2,, ())))).
      unfold super, pad, denote_pat, swap_list, swap_two.
      unfold scale.
      unfold Cmult.
      unfold outer_product.
      unfold denote.
      destruct (f 0), (f 1).
      destruct (size_wtype (Qubit ⊗ (Qubit ⊗ (Qubit ⊗ One)))%qc).
      simpl.
      destruct (zip_to 0 3 (pat_to_list (subst_pat [Some Qubit; Some Qubit; Some Qubit] p))).

      simpl. Msimpl.
      solve_matrix.
      symmetry.
      
      apply cexp0.
      
      simpl in IHn.
      replace (Cexp (2 * PI * INR (f 0) * 0)) with  C1 in IHn.
    
    unfold outer_product, f_to_vec, bool_to_ket.
    simpl.
    unfold shift, funbool_to_nat, funbool_to_list, binlist_to_nat.
    destruct n.
    + simpl.
      destruct (f 1).
      all: unfold denote_db_circuit.
      -- simpl. induction (f 0). all: destruct false, true.
         ++ simpl.   
         replace (Cexp (2 * PI * 1 * 1)) with C1.
         2: symmetry.
         2: apply cexp1.
         unfold scale.
                     destruct (c (qubit 0,, (qubit 1,, (qubit 2,, ())))).
            --- simpl. unfold super, pad, denote_pat, subst_pat, swap_list, swap_two, scale, Cmult, outer_product.
                simpl.
                Msimpl.
                destruct  (zip_to 0 3
      (pat_to_list
         ((fix subst_pat (Γ : Ctx) (w : WType) (p0 : Pat w) {struct p0} : Pat w :=
             match p0 in (Pat w0) return (Pat w0) with
             | () => ()
             | qubit x => qubit (subst_var Γ x)
             | bit x => bit (subst_var Γ x)
             | @pair W1 W2 p1 p2 => (subst_pat Γ W1 p1,, subst_pat Γ W2 p2)
             end) [Some Qubit; Some Qubit; Some Qubit] (Qubit ⊗ (Qubit ⊗ (Qubit ⊗ One))) p))).
                simpl.
                unfold I.
                +++ simpl.
                    unfold adjoint.
                    unfold Mmult.
                    simpl.
                    solve_matrix.
                    simpl.
                    solve_matrix.
                    all: simpl; Msimpl; solve_matrix.
                     
                     
         unfold Cmult, Mmult.
         unfold outer_product.
         unfold I, ket, adjoint.
         simpl.
         solve_matrix. 
         unfold pad, denote_pat, swap_list.
         simpl.
         unfold swap_two.
         simpl.
         unfold scale, Cmult, outer_product. simpl.
         unfold I.
         unfold Mmult, kron. simpl. Msimpl.
         solve_matrix.
         
         unfold outer_product.
         unfold scale.
         unfold bool_to_ket.
         simpl. Msimpl.
         solve_matrix.
         all: unfold WF_Matrix, ket. destruct (f 1).
         all: unfold kron.
         all: auto.
         all: solve_matrix.
         solve_matrix.
    rewrite sin_pos.
    solve_matrix.
    destruct id_circ.
    simpl.
    unfold hoas_to_db.
    solve_matrix.
    unfold denote_box.
   
    Msimpl.
    destruct (S n).
    
    simpl. destruct (S n0).
    apply IHn.

    
    unfold I.
    destruct (f 0%nat).
    
    unfold INR.
    destruct (f 0%nat).
    unfold adjoint, Cconj.
    solve_matrix.
    unfold bool_to_ket
    apply WF_swap_list_aux.
    unfold super.
    unfold compose_super.
    unfold super.
    unfold pad.
    unfold denote_pat.
    unfold swap_list.
    unfold zip_to.
    simpl.
    unfold swap_list_aux.
    Msimpl.     
    simpl.
    unfold bool_to_ket, funbool_to_nat.
    repeat rewrite Rmult_assoc.
    destruct (
    unfold outer_product.
    destruct 
    
    destruct (subst_var [Some Qubit; Some Qubit; Some Qubit; Some Qubit] 3%nat), (subst_var [Some Qubit; Some Qubit; Some Qubit; Some Qubit] 2%nat), (subst_var [Some Qubit; Some Qubit; Some Qubit; Some Qubit] 1%nat), (subst_var [Some Qubit; Some Qubit; Some Qubit; Some Qubit] 0%nat).
    all: simpl.
    all: unfold swap_two.
    all: simpl.
    all: unfold swap.
    all: unfold funbool_to_nat.
    all: unfold binlist_to_nat, funbool_to_list, shift; simpl.
    all: unfold INR.
    all: destruct (f 0%nat), (f 1%nat).
    all: simpl.
    all: replace (Cexp (2 * PI * 0 * 1)) with C1.
    all: replace (Cexp (2 * PI * 1 * 1)) with (-C1).
    all: unfold I.
    all: unfold kron.
    all: unfold Mmul.
    all: Msimpl.
    all: unfold apply_U.
    all: unfold super.
    all: simpl.
    all: try lia.
    all: unfold denote_ctrls.
    all: simpl.
    all: unfold phase_shift.
    all: simpl.
    all: Msimpl.
    all: unfold outer_product.
    all: unfold bool_to_ket.
    all: simpl.
    all: unfold ctrl_list_to_unitary_r.
    all: simpl.
    all: Msimpl.
    all: unfold kron.
    all: unfold adjoint.
    all: simpl.
    all: destruct (f 0%nat).
    all: destruct (f 1%nat).
    -- simpl.
       
       all: destruct (f 1%nat), (f 2%nat).
       unfold denote_db_circuit.
    induction (c (qubit 0%nat,, (qubit 1%nat,, (qubit 2%nat,, (qubit 3%nat,, ()))))).
    unfold hoas_to_db.
    -- simpl.
       destruct p.
      -- simpl.
         
         unfold pad.
         unfold denote_pat.
         simpl.
                  
         unfold subst_pat.
         unfold pat_to_list.
         unfold swap_list.
         unfold zip_to.
         unfold combine.
         
         
        destruct (hoas_to_db [Some Qubit; Some Qubit; Some Qubit; Some Qubit] p).
        unfold super.
        unfold pad.
        unfold denote_pat.
        unfold swap_list; simpl.
        unfold swap_two; simpl.
        unfold apply_U, super. simpl.
        Msimpl.
      unfold denote_db_circuit.
    unfold hoas_to_db.
    destruct (qubit 0%nat,, (qubit 1%nat,, (qubit 2%nat,, (qubit 3%nat,, ())))).
    unfold c.
    destruct c.
    all: simpl.
    induction (hoas_to_db [Some Qubit; Some Qubit; Some Qubit; Some Qubit] (c (qubit 0%nat,, (qubit 1%nat,, (qubit 2%nat,, (qubit 3%nat,, ())))))).
    induction (hoas_to_db_box (rotations 2 f)).
    unfold funbool_to_nat, shift; simpl.
    destruct (rotations 2 f).
    simpl; try lia.
    destruct (c (qubit 0%nat,, (qubit 1%nat,, (qubit 2%nat,, (qubit 3%nat,, ()))))).
    +  destruct (hoas_to_db [Some Qubit; Some Qubit; Some Qubit; Some Qubit] p).
        
(*ALTERNATE LEMMA VERSIONS; FIRST WOULD BE PREFERABLE FOR HOAS BUT PROBLEMATIC TO GO FROM DENSITY REO TO BOOL LIST, LATTER ALTERNATE FORMULATION
Lemma rotations_correct : forall n m (ρ: Density n),
    (n > 1)%nat ->
    denote_box true (rotations n m) ρ = 
      Cexp (2 * PI * (drop_and_dot (Den_to_StateVec ρ))) .* ρ.
                  

Lemma rotations_correct : forall n m x,
    (n > 1)%nat ->
    denote_box true (rotations n m) (bools_to_matrix (nat_to_binlist' x)) =
      Cexp (2 * PI * (hd (nat_to_binlist' x) * tail (nat_to_binlist' x))/2^n) .* (bools_to_matrix (nat_to_binlist' x)).
 *)
  Qed.
Lemma QFT_Sem: forall n f,
  (n > 0)%nat -> 
  denote_box true (QFT n) (outer_product (f_to_vec n f) (f_to_vec n f)) = 1 / √(2 ^ n) .* big_kron (map (fun j => ∣0⟩ .+ Cexp (2 * PI * INR (funbool_to_nat (n - j) (shift f j)) / 2 ^ (n - j)) .* ∣1⟩) (rev (enlist n))).
                                                                                                                                             Proof.
                                                                                                                                               intros n x Hn.
                                                                                                                                               generalize dependent x.
                                                                                                                                               destruct n; try lia.
                                                                                                                                               induction n; intro x.
                                                                                                                                               -
                                                                                                                                                 simpl qft.
                                                                                                                                                 simpl; Msimpl.
                                                                                                                                                 matrix_denote.
                                                                                                                                                 Msimpl.
                                                                                                                                                 all: solve_matrix.
                                                                                                                                                 all: simpl.

                                                                                                                                                 all: try (rewrite CL by lia; easy).
                                                                                                                                                 all: autorewrite with Cdist_db.
                                                                                                                                                 all: repeat rewrite Cmult_assoc; autorewrite with C_db.
                                                                                                                                                 all: repeat rewrite <- Cmult_assoc; autorewrite with C_db. *)
                                                                                                                                                 
                                                                                                                                                   
                                                                                                                                                 
                                                                      
                                                                                                                                                
                                                                                                                                                
                                                                                                                                                 
                                                                                                                                                 
                                                                                                                                                 
                                                                                                                                               
                                                                                                                                               













                                                                                                                                                                           
                                                                                            
                                                         
                                                                                                                                                 
