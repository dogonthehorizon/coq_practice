Section section_for_cut_example.
  Variables P Q R T : Prop.

  Hypotheses (H : P -> Q)
             (H0 : Q -> R)
             (H1 : (P -> R) -> T -> Q)
             (H2 : (P -> R) -> T).

  Theorem cut_example : Q.
  Proof.
    cut (P -> R).
    intro H3.
    apply H1;[assumption|apply H2; assumption].
    intro; apply H0; apply H; assumption.
  Qed.

(* I'm pretty sure there's an uneeded roundtrip in there, but,
   there are no more subgoals! *)
  Theorem cut_example' : Q.
  Proof.
    apply H1.
    intro H3.
    apply H0.
    apply H1.
    intros H4.
    apply H0.
    apply H.
    assumption.
    apply H2.
    intros H5.
    apply H0.
    apply H.
    assumption.
    apply H2.
    intros H6.
    apply H0.
    apply H.
    assumption.
  Qed.
End section_for_cut_example.