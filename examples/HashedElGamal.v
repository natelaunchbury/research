Require Import FCF.
Require Import RndGrpElem.
Require Import Encryption_PK.
Require Import DiffieHellman.
Require Import OTP.




Set Implicit Arguments.

Local Open Scope group_scope.


Section HashedElGamal.
  Context`{FCG : FiniteCyclicGroup}.
  Hypothesis GroupElem_EqDec : EqDec GroupElement.
  
  Definition HElGamalKeyGen :=
    x <-$ [0..order);
    k <-$ RndG;
    ret ((x, k), (g^x, k)).
 
  (* Hash function *)
  Variable l : nat.
  Variable H : forall l, GroupElement * GroupElement -> (Bvector l).
  (* Messages are now of length l which is presumably more convenient 
     Note that H is not a standard hash function as it may not expand *)

  (* H will have a property called "entropy smoothing" *)
  Hypothesis Entropy_smoothing : forall (x : GroupElement * GroupElement),
    comp_spec eq (ret (H l x)) (Rnd l).
  Lemma entropy_smoothing : forall x r, 
      evalDist (ret (H l x)) r == evalDist (Rnd l) r.
  Proof.
    intuition.
    eapply comp_spec_impl_eq.
    eapply comp_spec_consequence.
    apply Entropy_smoothing.
    intuition; subst; intuition.
  Qed.




  Definition HElGamalEncrypt (msg : (Bvector l)) (pubkey : GroupElement * GroupElement) :=
    y <-$ [0..order);
    [key,hkey] <-2 pubkey;
    h <- H l (hkey,key^y);
    v <- h xor msg;
    ret (g^y, v).
  
  Definition HElGamalDecrypt (ct : GroupElement * (Bvector l)) (prikey : nat) (hkey : GroupElement) :=
    [c1,c2] <-2 ct;
    h <- H l (hkey, c1^prikey);
    BVxor l h c2.
 
  Theorem HELGamal_correct : forall prikey pubkey msg ct hkey, 
      In ((prikey,hkey),(pubkey,hkey)) (getSupport HElGamalKeyGen) ->
      In ct (getSupport (HElGamalEncrypt msg (pubkey,hkey))) ->
      HElGamalDecrypt ct prikey hkey = msg. 
    Proof.
      unfold HElGamalKeyGen, HElGamalEncrypt, HElGamalDecrypt.
      intuition.
      repeat simp_in_support.
      repeat rewrite groupExp_mult.
      rewrite mult_comm.
      rewrite <- BVxor_assoc.
      rewrite BVxor_same_id.
      rewrite BVxor_id_l.
      reflexivity.
  Qed.

    Variable A_state : Set. 
    Variable A1 : (GroupElement * GroupElement) -> Comp ((Bvector l) * (Bvector l) * A_state). 
    Variable A2 : (GroupElement * (Bvector l) * A_state) -> Comp bool.

    (************          Security Games           ************)


    Definition G1 :=
      x <-$ [0..order);
      y <-$ [0..order);
      k <-$ RndG;
      a <- g^x;
      [m0,m1,s] <-$3 A1 (a, k);
      b <-$ {0,1}; 
      h <- H l (k, a^y);
      v <- if b then BVxor l h m0 else BVxor l h m1;
      b' <-$ A2 (g^y, v, s);
      ret (b ?= b').

    (* G1 is just the IND-CPA game of Hashed ElGamal *)
    Lemma HElGamal_INDCPA_G1 :
      Pr[IND_CPA_G HElGamalKeyGen HElGamalEncrypt A1 A2] == Pr[G1].
    Proof.
      unfold IND_CPA_G, HElGamalKeyGen, HElGamalEncrypt, G1.

      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      fcf_swap fcf_right.
      fcf_inline_first.
      fcf_skip.
      fcf_simp.
      fcf_swap fcf_right.
      fcf_skip.

      destruct x1.
      destruct p.
      fcf_swap fcf_right.
      fcf_skip.
      fcf_inline_first.
      fcf_skip.

      destruct x1; reflexivity.
    Qed.
      
    Definition G2 :=
      x <-$ [0..order);
      y <-$ [0..order);
      z <-$ [0..order);
      k <-$ RndG;
      a <- g^x;
      [m0,m1,s] <-$3 A1 (a, k); 
      h <- H l (k, g^z);
      b <-$ {0,1};
      v <-$ if b then ret (BVxor l h m0) else ret (BVxor l h m1);
      b' <-$ A2 (g^y, v, s);
      ret (b ?= b').

    (* Adversary that beats DDH using A1 and A2 *)
    Definition B (g : GroupElement * GroupElement * GroupElement) : Comp bool :=
      [gx,gy,gz] <-3 g;
      k <-$ RndG;
      [m0,m1,s] <-$3 A1 (gx, k);
      b <-$ {0,1};
      h <- H l (k, gz);
      v <- BVxor l h (if b then m0 else m1);
      b' <-$ A2 (gy, v, s);
      ret (b ?= b').
      
    Definition DDH0 := (@DDH0 _ _ _ _ _ g order).
    Definition DDH1 := (@DDH1 _ _ _ _ _ g order).
    Definition DDH_Advantage := (@DDH_Advantage _ _ _ _ _ g order).

    Hypothesis wf_RndG : well_formed_comp (RndG).
    Hypothesis wf_A1 : forall x, well_formed_comp (A1 x).
    Hypothesis wf_A2 : forall x, well_formed_comp (A2 x).

    (* G1 is equivalent to DDH0 - (gx, gy, gxy) *)
    Lemma G1_DDH0 :
      Pr[G1] == Pr[DDH0 B].
    Proof.
      unfold G1, DDH0, DiffieHellman.DDH0, B.
      fcf_skip.
      fcf_skip.
      fcf_inline_first.
      
      fcf_skip.
      fcf_simp.
      fcf_inline fcf_right.

      fcf_skip.

      destruct x2. 
      destruct p.

      fcf_inline fcf_right.

      fcf_skip.

      rewrite groupExp_mult.
      destruct x2. 
        fcf_inline_first. 
        fcf_skip.
        fcf_ret fcf_right.
        reflexivity.

        fcf_inline_first. 
        fcf_skip.
        fcf_ret fcf_right.
        reflexivity.
   Qed.


    (* G2 is equivalent to DDH1 - (gx, gy, gz) *)
    Lemma G2_DDH1 :
      Pr[G2] == Pr[DDH1 B].
    Proof.
      unfold G2, DDH1, DiffieHellman.DDH1, B.

      fcf_skip.
      fcf_skip.
      fcf_skip.

      fcf_inline_first.
      fcf_skip.

      fcf_simp.
      fcf_inline_first.
      fcf_skip.

      destruct x3.
      destruct p.

      fcf_inline_first.

      fcf_skip.

      fcf_simp.
      fcf_inline_first.
      

      destruct (Vector.hd x3).
      fcf_simp.
      
      fcf_skip.
      fcf_simp.
      intuition.

      fcf_simp.
      fcf_skip.
      fcf_simp.
      intuition.
  Qed.
      
    Lemma G1_G2_DDH :
      DDH_Advantage B == |Pr[G1] - Pr[G2]|.
    Proof.
      unfold DDH_Advantage, DiffieHellman.DDH_Advantage.
      apply ratDistance_eqRat_compat.
      symmetry.
      apply G1_DDH0.
      symmetry.
      apply G2_DDH1.
    Qed.

    
    Definition G3 := 
      x <-$ [0..order);
      y <-$ [0..order);
      z <-$ [0..order);
      k <-$ RndG;
      a <- g^x;
      [m0,m1,s] <-$3 A1 (a, k); 
      h <-$ {0,1}^l; 
      b <-$ {0,1};
      v <-$ if b then ret (BVxor l h m0) else ret (BVxor l h m1);
      b' <-$ A2 (g^y, v, s);
      ret (b ?= b').




    Lemma G2_G3 :
      Pr[G2] == Pr[G3].
    Proof.
      unfold G2, G3.
      do 5 fcf_skip.
      fcf_simp.
      fcf_swap fcf_right.
      fcf_skip.
      
      symmetry.
      rewrite <- evalDist_assoc.

      fcf_skip.
      destruct x3.

      fcf_ident_expand_r.
      fcf_rewrite_expr (evalDist (x3 <-$ ret H l (x2, g ^ x1) xor b; ret x3) x4 == evalDist (x3 <-$ ret H l (x2, g^x1); ret x3 xor b) x4).
      fcf_simp.
      intuition.
      fcf_skip.
      symmetry.
      apply entropy_smoothing.
      fcf_ident_expand_r.
      fcf_rewrite_expr (evalDist (x3 <-$ ret H l (x2, g ^ x1) xor b0; ret x3) x4 == evalDist (x3 <-$ ret H l (x2, g^x1); ret x3 xor b0) x4).
      fcf_simp.
      intuition.
      fcf_skip.
      symmetry.
      apply entropy_smoothing.
      intuition.
    Qed.




    Definition G4 :=
      x <-$ [0..order);
      y <-$ [0..order);
      z <-$ [0..order);
      k <-$ RndG;
      a <- g^x;
      [m0,m1,s] <-$3 A1 (a, k); 
      h <-$ {0,1}^l; 
      b <-$ {0,1};
      v <-$ {0,1}^l;
      b' <-$ A2 (g^y, v, s);
      ret (b ?= b').
   
    (* A one-time pad argument for bitvectors *)
    Theorem xor_OTP': 
      forall (x : Bvector l),
        comp_spec eq (Rnd l) (r <-$ Rnd l; ret (BVxor l r x)).
  
      eapply OTP_inf_th_sec_r; intuition.
      eapply BVxor_assoc.
      eapply BVxor_same_id.
      eapply BVxor_same_id.
      eapply BVxor_id_r.
  
      eapply comp_spec_rnd.   
    Qed.



    Lemma G3_G4 :
      Pr[G3] == Pr[G4].
    Proof.
      unfold G3, G4. 
      do 5 fcf_skip.
      fcf_simp.
      fcf_swap fcf_left.
      fcf_irr_r.
      apply well_formed_Rnd.
      fcf_skip.


      rewrite <- evalDist_assoc.
      fcf_skip.

      eapply comp_spec_impl_eq.
     
      eapply comp_spec_consequence.
      eapply comp_spec_symm.

      destruct x4.
      eapply xor_OTP'.
      eapply xor_OTP'.
      intuition.
      subst.
      intuition.
      subst.
      intuition.
      fcf_skip.
      
      reflexivity.
      intuition.
   Qed.
      


    Lemma G4_Onehalf :
      Pr[G4] == 1/2.
    Proof.
      unfold G4.
      do 5 fcf_irr_l.
      fcf_simp.
      fcf_irr_l.
      apply well_formed_Rnd.
      fcf_swap fcf_left.
      fcf_irr_l.
      apply well_formed_Rnd.
      fcf_swap fcf_left.
      fcf_irr_l.      
      fcf_compute.
    Qed.

      
        
    Theorem HElGamal_INDCPA :
      IND_CPA_Advantage HElGamalKeyGen HElGamalEncrypt A1 A2 ==
      DDH_Advantage B.
    Proof.
      unfold IND_CPA_Advantage.
      rewrite G1_G2_DDH.
      rewrite G2_G3.
      rewrite G3_G4.
      apply ratDistance_eqRat_compat.

      apply HElGamal_INDCPA_G1.
      
      symmetry.
      apply G4_Onehalf.   
    Qed.


    (* To Do : Currently using Hypthesis Entropy_smoothing 
     - Define what it means for H to be "entropy smoothing" 
     - encode this as a comp_spec theorem like xor_OTP' 
     - Find out how to swap out c1 for c1' if c1 => c1' in Prog logic
    *)