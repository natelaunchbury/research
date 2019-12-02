(* This file is an extension of Adam Petcher's ElGamal.v in fcf/src/FCF/examples/ *)

Set Implicit Arguments.

Require Import FCF.
Require Import RndGrpElem.
Require Import Encryption_PK.
Require Import DiffieHellman.
Require Import ElGamal.
Require Import OTP.



Local Open Scope group_scope.
Section ElGamalHomomorphism.
        
  Context`{FCG : FiniteCyclicGroup}.
  Hypothesis GroupElement_EqDec : EqDec GroupElement.
  
  (* ElGamal encryption has multiplicative homomorphism: 
    if c1 = E(m1) and c2 = E(m2) then 
       c1*c2 = E(m1*m2)
   *)

  Definition ElGamalKeygen :=
    m <-$ [0 .. order);
    ret (m, g^m).

  (* The ElGamal encryption procedure. *)
  Definition ElGamalEncrypt(msg key : GroupElement) := 
    m <-$ [0 .. order);
    ret (g^m, key^m * msg).

  (* The ElGamal decryption procedure. *)
  Definition ElGamalDecrypt(key : nat)(ct : GroupElement * GroupElement) :=
    [c1, c2] <-2 ct;
    s <- c1^key;
    (inverse s) * c2.

  (* We can prove that decryption is correct.  This procedure is deterministic, so this is just a typical Coq proof.  *)
  Theorem ElGamalDecrypt_correct : 
    forall (pubkey msg : GroupElement)(prikey : nat)(ct : GroupElement * GroupElement),
      In (prikey, pubkey) (getSupport ElGamalKeygen) ->
      In ct (getSupport (ElGamalEncrypt msg pubkey)) ->
      ElGamalDecrypt prikey ct = msg.

    unfold ElGamalKeygen, ElGamalEncrypt, ElGamalDecrypt.
    intuition. 
    (* simp_in_support is an automated tactic that breaks down hypotheses that state that some value is in the support of some distribution.  The resulting hypotheses will be more atomic and more directly useful.  *)
    repeat simp_in_support.
    rewrite <- associativity.
    repeat rewrite groupExp_mult.
    rewrite mult_comm.
    rewrite left_inverse.
    apply left_identity.
  Qed.

(* My work *)
(* ElGamal has the property that multiplying ciphertexts and then decrypting
   is the same as multiplying plaintexts (multiplicative homomorphism     *)
  Theorem ElGamal_mult_homo :
    forall (pubkey m1 m2 : GroupElement)(prikey : nat)(c1 c2 : GroupElement * GroupElement),
      In (prikey, pubkey) (getSupport ElGamalKeygen) ->
      In c1 (getSupport (ElGamalEncrypt m1 pubkey)) ->
      In c2 (getSupport (ElGamalEncrypt m2 pubkey)) ->  
      ElGamalDecrypt prikey ((fst c1)*(fst c2), (snd c1)*(snd c2)) = m1*m2.
  Proof.     
    unfold ElGamalKeygen, ElGamalEncrypt, ElGamalDecrypt.
    intuition. 
    repeat simp_in_support.
    simpl.
    repeat rewrite <- associativity.

    repeat rewrite groupExp_mult.

    (* Do some rearranging of terms *)
    rewrite associativity.
    rewrite (commutativity (g^(x1*x))).
    rewrite associativity.
    rewrite (commutativity m1).
    rewrite (commutativity m2).
    repeat rewrite <- associativity.
    rewrite associativity.
    rewrite (commutativity m2).
    rewrite <- associativity.

    f_equal.

    rewrite (mult_comm x1).
    rewrite (mult_comm x1).

    repeat rewrite <- groupExp_mult.
    rewrite groupExp_distrib.
    
    rewrite commutativity.

    rewrite associativity.
    rewrite left_inverse.

    rewrite right_identity.
    reflexivity.
Qed.   


(*  True but perhaps unnecessary 

    Lemma groupExp_distrib_commute : forall g x x0 x1, 
        ((g^x0 * g^x) ^ x1) = (g^(x1*x0) * g^(x1*x)).
    Proof.
      intros.
      replace (g0^(x1*x)) with (g0^(x*x1)).
      replace (g0^(x1*x0)) with (g0^(x0*x1)).
      repeat rewrite <- groupExp_mult.
      rewrite groupExp_distrib.
      reflexivity.

      rewrite mult_comm.
      reflexivity.
     
      rewrite mult_comm.
      reflexivity.
   Qed.


*)

End ElGamalHomomorphism.
