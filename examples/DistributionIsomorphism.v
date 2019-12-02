Require Import FCF.
Require Import LamportProof.

 (* f needs to be a bijection between the sampling domains
  generally this is between {0,1}^n and {0,1}^n *)


(* TODO: make some examples where the theorem is actually valuable *)


  (* perhaps the simplest possible example *)
  (* x and negb x clearly have the same probability 
   and there's an obvious bijection from {0,1} to {0,1}.
   Note, the other bijection won't work (it won't do anything) *)
  Lemma Bool_b_vs_negb :
    Pr[x <-$ {0,1}; ret x] == Pr[x <-$ {0,1}; ret negb x].
  Proof.
    eapply (distro_iso_eq (fun x => negb x) (fun x => negb x)).

  (* first and second goals *)
  (* f is a bijection with f_inv *)
    intuition.
    apply negb_involutive.

    intuition.
    apply negb_involutive.

  (* third goal *)
  (* f x is a possible value of c1 *)
    intuition.
    destruct x; unfold negb.
    eapply getSupport_In_Seq.
    unfold getSupport.
    apply in_getAllBvectors.
    unfold getSupport.
    instantiate (1:=Bvect_false 1).
    simpl.
    left; reflexivity.

    eapply getSupport_In_Seq.
    unfold getSupport.
    apply in_getAllBvectors.
    unfold getSupport.
    instantiate (1:=Bvect_true 1).
    simpl.
    left; reflexivity.

  (* fourth goal *)
  (* f x and x are equally likely out of c1 and c2 respectively *)
    intuition.
    assert (forall x, evalDist (m<-${0,1}^1; ret Vector.hd m) x ==
                      evalDist ({0,1}^1) [x]).
    fcf_compute.
    rewrite H0.
    rewrite H0.
    apply uniformity.
       
    
  (* now we have "skipped" the random sample and have (f x) instead of x *)
    intuition.
  Qed.

  

  (* does a slightly different return structure complicate anything? *)
  (* No, pretty much the same proof with a slightly different ending *)
  Lemma Bool_f_vs_t : 
    Pr[x <-$ {0,1}; ret (x?=false)] == Pr[x <-$ {0,1}; ret x?=true]. 
  Proof.
    eapply (distro_iso_eq (fun x => negb x) (fun x => negb x)); intuition.
    apply negb_involutive.
    apply negb_involutive.

    destruct x; unfold negb.
    eapply getSupport_In_Seq.
    unfold getSupport.
    apply in_getAllBvectors.
    unfold getSupport.
    instantiate (1:=Bvect_false 1).
    simpl.
    left; reflexivity.
    eapply getSupport_In_Seq.
    unfold getSupport.
    apply in_getAllBvectors.
    unfold getSupport.
    instantiate (1:=Bvect_true 1).
    simpl.
    left; reflexivity.

    fcf_compute.

    fcf_compute.
    exfalso.
    destruct x.
    apply n.
    reflexivity.
    unfold negb in e.
    inversion e.
  Qed.


  Lemma Bvect_constant_vs_constant : forall n a b, 
      Pr[x<-${0,1}^n; ret x?=a] == Pr[x<-${0,1}^n; ret x?=b].
  Proof.
    (*  The Distribution isomorphism theorem isn't worth applying
    unless you have something else AFTER the random variable is used 

    intuition.
    assert (Pr [x <-$ { 0 , 1 }^ n; ret x ?= a ] ==
            Pr [x <-$ { 0 , 1 }^ n; ret a ?= x ]).
    fcf_skip.
    rewrite eqb_symm.
    reflexivity.
    assert (Pr [x <-$ { 0 , 1 }^ n; ret x ?= b ] ==
            Pr [x <-$ { 0 , 1 }^ n; ret b ?= x ]).
    fcf_skip.
    rewrite eqb_symm.
    reflexivity.
    rewrite H. 
    rewrite H0.
    clear H H0.

    erewrite <- evalDist_event_equiv.
    erewrite <- evalDist_event_equiv.
    apply uniformity.
    *)

      
    intuition.
    destruct (a?=b) eqn:D.
    rewrite eqb_leibniz in D.
    subst b.
    reflexivity.
    (* want bijection f : {0,1}^n -> {0,1}^n such that
                     given a=/=b, if x=a then f x = b               
    *) 
    (* just swap a and b (swapping is involutive so f = f_inv) *)
    eapply (distro_iso_eq (fun x => if x?=a then b else (if x?=b then a else x))
                         (fun x => if x?=a then b else (if x?=b then a else x))). 

  (* if f a bijection? *)
    (* f (f_inv x) = x? *)
    intuition.
    destruct (x?=a) eqn:A.
    rewrite eqb_symm.
    rewrite D.
    rewrite eqb_refl.
    rewrite eqb_leibniz in A.
    rewrite A; reflexivity.

    destruct (x?=b) eqn:B.
    rewrite eqb_refl.
    rewrite eqb_leibniz in B.
    rewrite B; reflexivity.

    rewrite A.
    rewrite B.
    reflexivity.

    (* f_inv (f x) = x? *)
    intuition.
    destruct (x?=a) eqn:A.
    destruct (x?=b) eqn:B;
    rewrite eqb_symm;
    rewrite D;
    rewrite eqb_refl;
    rewrite eqb_leibniz in A;
    rewrite A; reflexivity.

    destruct (x?=b) eqn:B.
    rewrite eqb_refl.
    rewrite eqb_leibniz in B.
    rewrite B; reflexivity.

    rewrite A.
    rewrite B.
    reflexivity.

  (* is f x a possible value from c2? *)
    intuition.
    unfold getSupport.
    apply in_getAllBvectors.

  (* prob sampling (f x) = prob sampling x from c2? *)
    intuition.
    apply uniformity.

  (* then we just have to show the transformation works *)
    intuition.
    destruct (x?=a) eqn:A.
    rewrite eqb_leibniz in A.
    subst a.
    rewrite eqb_symm.
    reflexivity.

    destruct (x?=b) eqn:B.
    rewrite eqb_refl.
    reflexivity.
    rewrite A.
    reflexivity.
  Qed.



  Lemma Bvect_constant_vs_random : forall n a, 
    Pr[x <-$ {0,1}^n; ret x?=a] ==
    Pr[x <-$ {0,1}^n; y <-$ {0,1}^n; ret x?=y].
  Proof.
    intuition.
    (* this rearranging is purely for "moral" reasons *)
    fcf_swap fcf_right.
    fcf_irr_r; wftac.
    (* swap the random y and a *)
    (* we've already done this proof *)
    eapply Bvect_constant_vs_constant.
  Qed.

  (* RndNat is just an interpretation of a bitvector as an int *)
  Lemma RndNat_constant_vs_constant : forall l n m, 
      n < l -> m < l -> 
      Pr[a<-$[0..l); ret a?=n] == Pr[a<-$[0..l); ret a?=m].
  Proof.
    intuition.
    destruct (n?=m) eqn:D.
    rewrite eqb_leibniz in D.
    rewrite D; reflexivity.

    (* swap n and m again *)
    eapply (distro_iso_eq (fun x => if x?=n then m else (if x?=m then n else x))
                          (fun x => if x?=n then m else (if x?=m then n else x))).
    intuition.
    destruct (x?=n) eqn:N.
    rewrite eqb_symm.
    rewrite D.
    rewrite eqb_refl.
    rewrite eqb_leibniz in N.
    rewrite N; reflexivity.

    destruct (x?=m) eqn:M.
    rewrite eqb_refl.
    rewrite eqb_leibniz in M.
    rewrite M; reflexivity.

    rewrite N.
    rewrite M.
    reflexivity.

    intuition.
    destruct (x?=n) eqn:N.
    rewrite eqb_symm.
    rewrite D.
    rewrite eqb_refl.
    rewrite eqb_leibniz in N.
    rewrite N; reflexivity.

    destruct (x?=m) eqn:M.
    rewrite eqb_refl.
    rewrite eqb_leibniz in M.
    rewrite M; reflexivity.

    rewrite N.
    rewrite M.
    reflexivity.

    intuition.
    apply in_getSupport_RndNat.
    destruct (x?=n).
    assumption.
    destruct (x?=m).
    assumption.
    apply RndNat_support_lt in H1; assumption.

    intuition.
    apply RndNat_support_lt in H1.
    apply RndNat_uniform;
    destruct (x?=n);
    destruct (x?=m);
    assumption.

    intuition.
    destruct (x?=m) eqn:M, (x?=n) eqn:N.
    rewrite eqb_leibniz in M.
    rewrite eqb_leibniz in N.
    subst.
    rewrite eqb_refl in D.
    inversion D.

    rewrite eqb_refl.
    reflexivity.

    rewrite eqb_symm.
    rewrite D.
    reflexivity.

    rewrite N.
    reflexivity.
  Qed.

  (* instead of swapping values, we might shift them instead *)
  Lemma RndNat_constant_vs_constant2 : forall l n m,  
      l > 0 -> n < l -> m < l -> 
      Pr[a<-$[0..l); ret a?=n] == Pr[a<-$[0..l); ret a?=m].
  Proof.
    intros l n m Hl Hn Hm.
    (* let's shift all the values so that f x = m when x = n *)
    eapply (distro_iso_eq (fun x => (x + (n + (l - m))) mod l)
                          (fun x => (x + (m + (l - n))) mod l)).
    intuition.
    rewrite Nat.add_mod_idemp_l; try omega.
    rewrite plus_assoc.
    rewrite plus_assoc.
    replace (x+m+(l-n)+n+(l-m))%nat with (x+(n+(l-n))+(m+(l-m)))%nat by omega.   
    rewrite <- le_plus_minus; try omega.
    rewrite <- le_plus_minus; try omega.
    rewrite plus_comm.
    rewrite <- Nat.add_mod_idemp_l; try omega.
    rewrite Nat.mod_same; try omega.
    rewrite plus_0_l.
    rewrite plus_comm.
    rewrite <- Nat.add_mod_idemp_l; try omega.
    rewrite Nat.mod_same; try omega.
    rewrite plus_0_l.
    rewrite Nat.mod_small. 
    reflexivity.
    apply RndNat_support_lt; assumption.

    (* only difference is symmetric "replace" *)
    intuition.   
    rewrite Nat.add_mod_idemp_l; try omega.
    rewrite plus_assoc.
    rewrite plus_assoc.
    replace (x+n+(l-m)+m+(l-n))%nat with (x+(n+(l-n))+(m+(l-m)))%nat by omega. 
    rewrite <- le_plus_minus; try omega.
    rewrite <- le_plus_minus; try omega.
    rewrite plus_comm.
    rewrite <- Nat.add_mod_idemp_l; try omega.
    rewrite Nat.mod_same; try omega.
    rewrite plus_0_l.
    rewrite plus_comm.
    rewrite <- Nat.add_mod_idemp_l; try omega.
    rewrite Nat.mod_same; try omega.
    rewrite plus_0_l.
    rewrite Nat.mod_small. 
    reflexivity.
    apply RndNat_support_lt; assumption.

    intuition.
    apply in_getSupport_RndNat.
    apply Nat.mod_upper_bound.
    omega.

    intuition.
    apply RndNat_uniform.
    apply Nat.mod_upper_bound.
    omega.
    apply RndNat_support_lt.
    assumption.
    
    intros x Hx.
    (* now we need some machinery *)
    (* note that f was chosen so that the following holds *)
    assert ((x + (n + (l - m)))%nat mod l = n <-> x = m).
      split; intro H.
      + assert ((x+(l-m))%nat mod l = 0%nat).
        admit.

     
        rewrite Nat.mod_divides in H0; intuition.
        inversion H0 as [c Hc].
        clear H0.
        destruct c.
        omega.
        destruct c.
        omega. 

        (* false since minimizing d and maximizing c is still < 2*l *)
        exfalso.
        rewrite <- mult_n_Sm in Hc.
        rewrite <- mult_n_Sm in Hc.
        assert (l + l <= l*c + l + l)%nat.
        destruct c.
        omega.
        apply plus_le_compat_r.
        rewrite plus_comm.
        destruct (l*S c)%nat; omega.
        apply RndNat_support_lt in Hx.
        omega.

      + subst x.
        rewrite plus_assoc.
        rewrite plus_comm at 1.
        rewrite plus_assoc.
        replace (l - m + m)%nat with l by omega.
        rewrite <- Nat.add_mod_idemp_l; try omega.
        rewrite Nat.mod_same; try omega.
        rewrite plus_0_l.
        rewrite Nat.mod_small.
        reflexivity.
        assumption.      
    
      + destruct ((x+(n+(l-m)))%nat mod l ?= n) eqn:?.
        rewrite eqb_leibniz in Heqb.
        apply H in Heqb.
        rewrite Heqb.
        rewrite eqb_refl.
        reflexivity.
        rewrite eqb_false_iff in Heqb.
        intuition.
        destruct (x?=m) eqn:M.
        rewrite eqb_leibniz in M.
        intuition.
        reflexivity.
  Admitted.

  Lemma RndNat_constant_vs_random : forall l n,
      l > 0 -> n < l -> 
      Pr[x <-$ [0..l); ret x ?= n] ==
      Pr[x <-$ [0..l); y <-$ [0..l); ret x?=y].
  Proof.
    intuition.
    (* let's skip the moral rearranging *)
    fcf_irr_r; try apply well_formed_RndNat.
    (* now we have to rearrange the goal *)
    assert (Pr [y <-$ [ 0 .. l); ret x ?= y] == Pr[y <-$ [ 0 .. l); ret y ?= x])
      by (fcf_skip; rewrite eqb_symm; reflexivity).  
    rewrite H2.
    eapply RndNat_constant_vs_constant.
    assumption.
    eapply RndNat_support_lt.
    assumption.
  Qed.


 
  (* There's no bijection between these since they're different sizes 
   (are we sure distro_iso_eq doesn't apply?) *)
  (* Is there a way to make this argument (since {odd [0..l)} + {even [0..l)})?*)
  Lemma Bool_vs_evenRndNat : forall l,
      l > 0 -> (odd l = true) ->
      Pr[n <-$ [0..l); ret (even n ?= true)] ==
      Pr[b <-$ {0,1}; ret b].
  Proof.
    intuition.
    Admitted.
