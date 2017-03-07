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
  (* Note that inline proofs are not recommended by Bertot *)
  Proof (fun (H:P->P->Q)(p:P) => H p p).
End taken_to_the_extreme.

Print imp_trans.
Print imp_trans'.
Print L1.
Print delta.

(* Regular ol' tactics *)
Theorem compose_example : (P -> Q -> R) -> (P -> Q) -> (P -> R).
Proof.
  intros H H' p.
  apply H.
  apply p.
  apply H'.
  assumption.
Qed.

(* 'Tacticals', or, higher-order tactics. *)
Theorem compose_example' : (P -> Q -> R) -> (P -> Q) -> (P -> R).
Proof.
  intros H H' p.
  apply H;[assumption | apply H'; assumption].
Qed.

(* Regular ol' tactics *)
Lemma L3 : (P->Q)->(P->R)->(P->Q->R->T)->P->T.
Proof.
  intros H H0 H1 p.
  apply H1.
  assumption.
  apply H.
  assumption.
  apply H0.
  assumption.
Qed.

(* 'Tacticals', or, higher-order tactics. Featuring ID. *)
Lemma L3' : (P->Q)->(P->R)->(P->Q->R->T)->P->T.
Proof.
  intros H H0 H1 p.
  apply H1;[idtac | apply H | apply H0]; assumption.
Qed.