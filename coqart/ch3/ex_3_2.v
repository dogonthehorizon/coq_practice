(* Exercise 3.2: Using the basic tactics 'assumption', 'intros', and 'apply',
 * prove the following lemmas:
 *)

Variables P Q R T : Prop.

Lemma id_P : P -> P.
Proof.
  intros p.
  assumption.
Qed.

Lemma id_PP : (P -> P) -> (P -> P).
Proof.
  intros H p.
  apply H.
  assumption.
Qed.

Lemma imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros H H' p.
  apply H'.
  apply H.
  assumption.
Qed.

Lemma imp_perm : (P -> Q -> R) -> (Q -> P -> R).
Proof.
  intros H q p.
  apply H.
  apply p.
  apply q.
Qed.

Lemma ignore_Q : (P -> R) -> P -> Q -> R.
Proof.
  intros H p q.
  apply H.
  apply p.
Qed.

Lemma delta_imp : (P -> P -> Q) -> P -> Q.
Proof.
  intros H p.
  apply H.
  apply p.
  apply p.
Qed.

Lemma delta_impR : (P -> Q) -> (P -> P -> Q).
Proof.
  intros H p.
  apply H.
Qed.

Lemma diamond : (P -> Q) -> (P -> R) -> (Q -> R -> T) -> P -> T.
Proof.
  intros H H' H'' p.
  apply H''.
  apply H.
  apply p.
  apply H'.
  apply p.
Qed.

Lemma weak_peirce : ((((P -> Q) -> P) -> P) -> Q) -> Q.
Proof.
  intros H.
  apply H.
  intros H'.
  apply H'.
  intros H''.
  apply H.
  intros H'''.
  apply H''.
Qed.