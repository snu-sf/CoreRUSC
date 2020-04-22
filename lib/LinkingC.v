Require Import CoqlibC.

Set Implicit Arguments.



Class Linker (A: Type) := {
  link: A -> A -> option A;
  linkorder: A -> A -> Prop;
  linkorder_refl: forall x, linkorder x x;
  linkorder_trans: forall x y z, linkorder x y -> linkorder y z -> linkorder x z;
  link_linkorder: forall x y z, link x y = Some z -> linkorder x z /\ linkorder y z
}.

Inductive link_res (A: Type): Type :=
| empty
| fail
| success: A -> link_res A.

Arguments empty [A].
Arguments fail [A].

Fixpoint link_list_aux X `{Linker X} (xs: list X): link_res X :=
  match xs with
  | [] => empty
  | x0 :: tl =>
    match link_list_aux tl with
    | empty => success x0
    | fail => fail
    | success x1 =>
      match link x0 x1 with
      | Some x => success x
      | None => fail
      end
    end
  end.

Definition link_list X `{Linker X} (xs: list X): option X :=
  match link_list_aux xs with
  | empty => None (* Note that we are not giving semantics to empty programs. *)
  | success x => Some x
  | fail => None
  end.

Lemma link_list_cons
      X `{Linker X} hd tl restl res
      (TL: link_list tl = Some restl)
      (HD: link hd restl = Some res):
    <<LINK: link_list (hd :: tl) = Some res>> /\ <<LINKORDER: Forall (fun x => linkorder x res) (hd :: tl)>>.
Proof.
  split; red.
  - unfold link_list in *. des_ifs; ss; des_ifs.
  - eapply link_linkorder in HD. des. econs; auto. clear HD. unfold link_list in TL. des_ifs.
    generalize dependent restl. generalize dependent res.
    induction tl as [|h l]; auto. i. econs; unfold link_list_aux in *; des_ifs.
    { eapply link_linkorder in Heq1. des. eapply linkorder_trans; eauto. }
    { destruct l; auto. des_ifs. }
    eapply IHl; eauto. eapply link_linkorder in Heq1. des. eapply linkorder_trans; eauto.
Qed.

Lemma link_list_linkorder
      X `{Linker X} xs xs_res
      (LINK: link_list xs = Some xs_res):
    <<LINKORDER: Forall (fun x => linkorder x xs_res) xs>>.
Proof.
  destruct xs as [| hd tl]; auto.
  unfold link_list in LINK. des_ifs. unfold link_list_aux in Heq. des_ifs; fold link_list_aux in *.
  { destruct tl; ss. econs. apply linkorder_refl. econs. des_ifs. }
  econs. { eapply link_linkorder in Heq1. des. auto. }
  assert (link_list tl = Some x).
  { unfold link_list. rewrite Heq0. auto. }
  exploit link_list_cons; eauto. i. des.
  inv LINKORDER. auto.
Qed.

Lemma link_list_cons_inv
      X `{Linker X} hd tl res
      (LINK: link_list (hd :: tl) = Some res)
      (LEN: tl <> []):
    exists restl, <<TL: link_list tl = Some restl>> /\ <<HD: link hd restl = Some res>>.
Proof.
  unfold link_list in LINK. des_ifs. unfold link_list_aux in Heq. des_ifs; fold link_list_aux in *.
  { destruct tl; ss. econs. des_ifs. }
  exists x. split; auto. unfold link_list. rewrite Heq0. auto.
  Unshelve. auto.
Qed.

