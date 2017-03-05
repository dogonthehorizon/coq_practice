Variables P Q R T : Prop.

Section Minimal_propositional_logic.

  (* Using explicit tactics *)
  Theorem imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
  Proof.
    intros H H' p.
    apply H'.
    apply H.
    assumption.
  Qed.

  (* Getting Coq to help us *)
  Theorem imp_trans' : (P -> Q) -> (Q -> R) -> P -> R.
  Proof.
    auto.
  Qed.
End Minimal_propositional_logic.

Section example_of_assumption.
  Hypothesis H : P -> Q -> R.

  (* More assumptions! *)
  Lemma L1 : P -> Q -> R.
  Proof.
    assumption.
  Qed.
End example_of_assumption.

Section taken_to_the_extreme.
  (* We can also define proofs in terms of functions.
   * Thanks Curry and Howard!
   *)
  Theorem delta : (P -> P -> Q) -> P -> Q.
  Proof (fun (H:P->P->Q)(p:P) => H p p).
End taken_to_the_extreme.

Print imp_trans.
Print imp_trans'.
Print L1.
Print delta.
