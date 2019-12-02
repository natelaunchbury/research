Require Import FCF.

(* The fundamental lemma of distributions lets you bound the distance between 
   events by the probability of a "bad" event occurring. It is useful if your
   final goal is a distance bound on the advantage of a security game based on 
   another security game plus a term, i.e. A_Adv = B_Adv + q. 

   To use the fundamental lemma, you want games to return values of the form 
       (P a, B a)
   where (P a) is the value of interest and (B a) is bool indicator of the badness
   
   Note: you can also just use return type "option A", see Section unOption below

   When games do not have any badness, link them to games with badness by, 
       Lemma ... Pr[G1] == Pr[x <-$ G2; ret (fst x)]. 

   You will then have a series of lemmas with the forms: 
           "G2_G3_same_badness"
     - Lemma ... Pr[x <-$ G2; ret (snd x)] == Pr[x <-$ G3; ret (snd x)]
           "G2_G3_eq_until_bad"   - requires "fcf_compute"
     - Lemma ... forall z, evalDist G2 (z,false) == evalDist G3 (z,false)
           "G2_badness_small"
     - Lemma ... Pr[x <-$ G2; ret (snd x)] <= q/p    (for some q p)

   The final lemma will then be, 
      Lemma ... forall z,
        |evalDist G2 z - evalDist G3 z| <= q/p        

   and can be shown using the "fundamental_lemma_h"
*)

Section FundamentalLemma.

  Variable n : nat.
  Hypothesis nz : n > 0.
  Variable v : (Bvector n).

  (* Simple bitvector sampling and matching *)
  Definition G1 :=
    v' <-$ {0,1}^n;
    ret v?=v'.  

  (* Now we consider sampling the all-false vector to be "bad" *)
  Definition G2 :=
    v' <-$ {0,1}^n;
    bad <-$ ret (Bvect_false n ?= v');
    ret (v?=v', bad).

  (* When the "bad" event occurs, we miss our target *)
  Definition G3 := 
    v' <-$ {0,1}^n;
    bad <-$ ret (Bvect_false n ?= v');
    v'' <- if bad then Bvect_true n else v';
    ret (v?=v'', bad).


  Lemma G1_G2_link :
    Pr[G1] == Pr[x <-$ G2; ret (fst x)].
  Proof.
    unfold G1, G2.
    fcf_simp.
    fcf_inline fcf_right.
    fcf_skip.
    fcf_inline fcf_right.
    fcf_simp.
    unfold fst.
    reflexivity.
  Qed.

  Lemma G2_G3_same_badness :
    Pr[x1 <-$ G2; ret (snd x1)] == Pr[x <-$ G3; ret (snd x)]. 
  Proof.
    unfold G2, G3.
    fcf_inline_first. 
    fcf_skip.
    fcf_inline_first.
    fcf_irr_r.
    apply well_formed_Ret.

    destruct x0; intuition.
    fcf_simp.
    unfold snd.
    repeat simp_in_support.
    rewrite H0.
    reflexivity.

    fcf_simp.
    unfold snd.
    repeat simp_in_support.
    rewrite H0.
    reflexivity.
  Qed.


  (* The statement captures that the "bad" event doesn't occur, 
     but how does the proof? *)
  (* by computing the probabilities after function application ("fcf_compute") *)
  Lemma G2_G3_eq_until_bad :
    forall z, 
    evalDist G2 (z,false) == evalDist G3 (z,false).
  Proof.
    unfold G2, G3.
    intuition.

    fcf_skip.
    fcf_simp.

    (* Here if we destruct only 1 case will be "true" *)
    fcf_compute.
  Qed.

  Lemma G2_badness_small :
     Pr[x <-$ G2; ret (snd x)] <= 1/expnat 2 n. 
  Proof.
    unfold G2.
    fcf_inline_first.
    fcf_at fcf_inline fcf_left 1%nat.
    unfold snd.

    (* could also "apply RndNat_eq_any" from RndInList.v *)    
    simpl.
    rewrite (@sumList_exactly_one _ (Bvect_false n)).
    rewrite eqbBvector_complete.
    destruct (EqDec_dec bool_EqDec true true); intuition.
    rewrite ratMult_1_r.
    reflexivity.

    apply getAllBvectors_NoDup.

    apply in_getAllBvectors.

    intuition.
    destruct (EqDec_dec bool_EqDec (eqbBvector (Bvect_false n) b) true); intuition.
    apply eqbBvector_sound in e.
    rewrite e in H0.
    intuition.

    rewrite ratMult_0_r.
    reflexivity.
  Qed.

  Lemma G2_G3_fundamental : forall z,       
  | evalDist (x <-$ G2; ret fst x) z - evalDist (x <-$ G3; ret fst x) z|
  <= 1/expnat 2 n.
    Proof.
      intuition.
      eapply leRat_trans.
      eapply fundamental_lemma_h.
      eapply G2_G3_same_badness.
      eapply G2_G3_eq_until_bad.
      eapply G2_badness_small.      
    Qed.

    (* Some security definition you want to achieve *)
    Definition SecurityDef_Advantage G1 (G2 : Comp (bool * bool)) eps :=
      |Pr[G1] - Pr[x <-$ G2; ret fst x]| <= eps.

    Theorem G1_G3 :
      SecurityDef_Advantage G1 G3 (1/expnat 2 n).
    Proof.
      unfold SecurityDef_Advantage.
      rewrite G1_G2_link.
      apply G2_G3_fundamental.
    Qed.



    (* This section explores using more conventional function programming 
   techniques such as the "option" monad to capture failure/badness. 
    *)
   Section unOption. 

    Require Import RndInList.

    Lemma expnat_eq_pow : forall n,
        1/2^n == 1/expnat 2 n.
    Proof.
      unfold expnat, "^".
      intuition.
    Qed.

    (* Let's try a slightly different idea (and more useful) *)
    Definition Gopt1 :=
      v' <-$ {0,1}^n;
      ret (if Bvect_false n ?= v' then None else Some (v?=v')).

    Definition unOption {A : Set} {eqdAbool : EqDec (A*bool)}
               (c : Comp (option A)) (default : A) :=
      x <-$ c;
      match x with 
      | Some x' => ret (x', false)
      | None    => ret (default, true)                 
      end.

    Definition Gopt2 (default : bool) :=
      v' <-$ {0,1}^n;
      ret (if Bvect_false n ?= v' then (default,true) else (v?=v',false)).
               
    Lemma Gopt1_Gopt2_cs_unOption :
      forall d, 
      comp_spec eq (unOption Gopt1 d) (Gopt2 d).
    Proof.
      unfold Gopt1, Gopt2.
      unfold unOption.
      intuition.
      fcf_inline_first.
      fcf_skip.
      destruct (Bvect_false n ?= b); reflexivity.
    Qed.

    Lemma Gopt1_Gopt2_pr_unOption :
      forall d z,
       evalDist (unOption Gopt1 d) z == evalDist (Gopt2 d) z. 
    Proof.
      intuition.
      eapply comp_spec_impl_eq.
      eapply comp_spec_consequence.
      eapply Gopt1_Gopt2_cs_unOption.
      intuition.
      subst.
      assumption.
      subst.
      assumption.
    Qed.


    Lemma G3_Gopt1_same_badness : forall d,
      Pr[x<-$G3; ret snd x] == Pr[x<-$(unOption Gopt1 d); ret snd x]. 
    Proof.
      unfold G3, Gopt1, unOption.
      intuition.
      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      destruct (Bvect_false n ?= x) eqn:?.
      fcf_simp.
      unfold snd.
      reflexivity.

      fcf_simp.
      unfold snd.
      reflexivity.
    Qed.
               
    Lemma G3_Gopt1_eq_until_bad :
      forall z d,
        evalDist G3 (z,false) == evalDist (unOption Gopt1 d) (z,false).
    Proof.
      unfold G3, Gopt1, unOption.
      intuition.
      fcf_inline_first.
      fcf_skip.
      destruct (Bvect_false n ?= x).
      fcf_simp.
      fcf_compute.
      fcf_simp.
      fcf_compute.
    Qed.

    Lemma G3_badness_small :
      Pr[x <-$ G3; ret snd x] <= 1/expnat 2 n.
    Proof.
      unfold G3.
      fcf_inline_first.
      fcf_at fcf_inline fcf_left 1%nat.
      unfold snd.
      rewrite RndNat_eq_any.
      rewrite expnat_eq_pow. 
      intuition.    
    Qed.

    Theorem G3_Gopt1_fundamental : forall z d,
      |evalDist (x<-$G3; ret fst x) z -
       evalDist (x<-$(unOption Gopt1 d); ret fst x) z| <= 1/expnat 2 n.
    Proof.
      intuition.
      eapply leRat_trans.
      eapply fundamental_lemma_h.
      apply G3_Gopt1_same_badness.
      intuition.
      revert d.
      revert a.
      apply G3_Gopt1_eq_until_bad.
      apply G3_badness_small.
    Qed.

    Theorem G3_Gopt2_fundamental : forall z d,
      |evalDist (x<-$G3; ret fst x) z -
       evalDist (x<-$(Gopt2 d); ret fst x) z | <= 1/expnat 2 n.
    Proof.
      intuition.
      eapply leRat_trans.
      Focus 2.
      eapply G3_Gopt1_fundamental.
      Focus 1.
      eapply eqRat_impl_leRat.
      eapply ratDistance_eqRat_compat.
      reflexivity.

      symmetry.
      (* I feel like this should imply what we want *)
      pose proof Gopt1_Gopt2_pr_unOption.
      unfold Gopt1, Gopt2, unOption.
      fcf_inline_first.
      fcf_skip. 
      destruct (Bvect_false n ?= x); fcf_simp; intuition.
      reflexivity.
    Qed.

    (* Conclusion: 
      You can sequence games that return "option A" as if they returned "A*bool" 
      like is generally required by the fundamental lemma. This allows more 
      natural programming in the functional style. 
      This can be done by using "unOption G_ d" everywhere or linking the 
      games with "option" to a "(P a, B a)" game 

      Below you can see another idea: turning option A into (option A * bool) 
      this is perhaps the most natural transformation for actual code
     *)

    Definition makeOptionBadnessPair {A : Set} (a : option A) :=
      match a with
      | None => (a,true)
      | Some _ => (a,false)
      end. 

    Definition Gopt2' :=
      v' <-$ {0,1}^n;
      ret (if Bvect_false n ?= v' then (None,true) else (Some (v?=v'),false)).

    Definition Gopt3 :=
      x <-$ Gopt1;
      ret makeOptionBadnessPair x.

    Theorem Gopt2'_Gopt3 : forall z,
        evalDist Gopt2' z == evalDist Gopt3 z.
    Proof.
      unfold Gopt2', Gopt3, Gopt1, makeOptionBadnessPair.
      intuition.
      fcf_inline_first.
      fcf_skip.
      destruct (Bvect_false n ?= x); fcf_simp; try reflexivity. 
    Qed.
      
  End unOption.

End FundamentalLemma.
    
    
 
      
  Lemma uniformity_pr : forall n (x1 x2 : Bvector n), 
      Pr[a<-${0,1}^n; ret x1 ?= a] == Pr[a<-${0,1}^n; ret x2 ?= a].
    Proof.
      intuition.
      rewrite <- (@evalDist_event_equiv _ _ (Rnd n) x1).
      rewrite <- (@evalDist_event_equiv _ _ (Rnd n) x2).
      apply uniformity.
    Qed.
    
     

   (* Not used, just scratch *)
    Lemma should_be_obvious : forall n (v : Bvector n),
        true :: v <> false :: v.
    Proof.
      intros.
      Unset Printing Notations. 
      unfold not.
      intros.
      Set Printing Notations.
      inversion H.
    Qed.            

    Lemma Bvect_false_true_ne : forall n,
        n > 0 -> 
        Bvect_false n <> Bvect_true n.
    Proof.
      intros.
      unfold Bvect_false, Bvect_true.
      induction n.
      inversion H.
      simpl.
      intros X.
      inversion X.      
    Qed.



    Require Import RndInList.

    (* This would be useful, for now, just "fcf_at fcf_inline _ 1%nat" *)
    Lemma useful1 : forall n x v,
        nz n -> 
        In x (getSupport ({0,1}^n)) ->
        Pr[ret v ?= x] == Pr[x <-$ {0,1}^n; ret v?=x].
    Proof.
      intuition.
      fcf_irr_r; wftac.
      eapply eqRat_trans.
      instantiate (1:= 1/expnat 2 n).      

    Abort.


    Lemma useful : forall x v,
      In x (getSupport ({0,1}^n)) ->
      Pr[ret v ?= x] <= 1/expnat 2 n.
    Proof.
      intuition.
      simpl.
      unfold getSupport in H. 


    Abort.

    (* First attempt at unOption*)
    Definition G4 :=
      v' <-$ {0,1}^n;
      bad <-$ ret (Bvect_false n ?= v');
      v'' <- if bad then None else Some (v?=v');
      ret (v'', bad).
                             
    Definition unSome {A : Type} (x : option A) (defaultA : A) :=
      match x with
      | Some x' => x'
      | None    => defaultA
      end.
            
    Lemma G3_G4_same_badness : 
      Pr[x<-$G3; ret snd x] == Pr[x<-$G4; ret snd x].
    Proof.
      unfold G3, G4.
      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      fcf_simp.
      unfold snd.
      reflexivity.
    Qed.

    Lemma G3_G4_unOption_until_bad :
      forall z, 
        evalDist (x<-$G3; ret x) (z,false) ==
        evalDist (x<-$G4; ret (unSome (fst x) false, snd x)) (z,false).
    Proof.
      unfold G3, G4.
      intuition.

      fcf_inline_first.
      fcf_skip.

      fcf_compute.
    Qed.


    Lemma G4_none_small :
      Pr[x<-$G4; ret snd x] <= 1/expnat 2 n.
    Proof.
      unfold G4.
      fcf_inline_first.
      fcf_at fcf_inline fcf_left 1%nat.
      unfold snd.
      rewrite RndNat_eq_any.
      rewrite expnat_eq_pow.
      intuition.
    Qed.

    Theorem G3_G4_fundamental : forall z,
     |evalDist (x<-$G3; ret fst x) z -
      evalDist (x<-$G4; ret (unSome (fst x) false)) z|
     <= 1/expnat 2 n.
    Proof.
      intuition.
      eapply leRat_trans.
      (*eapply fundamental_lemma_h.*)
    Abort.

