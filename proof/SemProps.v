Require Import UNIVERSE.
Require Import Events.
Require Import CoqlibC.
Require Import LinkingC.
Require Import JMeq.
Require Import Smallstep.
Require Import Simulation.

Require Import BehaviorsC.
Require Import ModSem Mod Sem.
Require Import SimSymb SimMem.

Require Import ModSemProps.

Set Implicit Arguments.


(* TODO: better namespace? *)
Lemma includes_refl
      sk:
    <<INCL: SkEnv.includes (Sk.load_skenv sk) sk>>.
Proof.
  eapply SkEnv.linkorder_includes; et.
  eapply linkorder_refl.
Qed.




Lemma link_includes
      p sk_link_src
      (LINK: link_sk p = Some sk_link_src)
      md
      (IN: In md p):
    SkEnv.includes (Sk.load_skenv sk_link_src) (Mod.sk md).
Proof.
  unfold link_sk in *.
  (* TODO: can we remove `_ LINK` ? *)
  (* Arguments link_list_linkorder [_]. *)
  (* Arguments link_list_linkorder: default implicits. *)
  hexploit (link_list_linkorder _ LINK); et. intro LOS; des.
  rewrite Forall_forall in *. exploit (LOS md); et.
  { rewrite in_map_iff. esplits; et. }
  intro LO.
  eapply SkEnv.linkorder_includes; et.
Qed.

Theorem link_list_preserves_wf_sk
        p sk_link
        (LINK: link_sk p = Some sk_link)
        (WFSK: forall md, In md p -> <<WF: Sk.wf md >>):
    <<WF: Sk.wf sk_link>>.
Proof.
  unfold link_sk in *. ginduction p; ii; ss. unfold link_list in LINK. des_ifs_safe. ss.
  destruct (link_list_aux (map Mod.sk p)) eqn:T; ss.
  { clarify. destruct p; ss; des_ifs. eapply WFSK. eauto. }
  des_ifs. rename t into tl. rename a into hd. specialize (IHp tl). exploit IHp; eauto.
  { unfold link_list. des_ifs. }
  i; des. eapply (Sk.link_preserves_wf_sk hd tl); et. eapply WFSK; et.
Qed.



Module AUX.

  Inductive find_fptr_owner (mss: list ModSem.t) (fptr: val) (ms: ModSem.t): Prop :=
  | find_fptr_owner_intro
      (MODSEM: In ms mss)
      if_sig
      (INTERNAL: Genv.find_funct ms.(ModSem.skenv) fptr = Some (Internal if_sig))
  .

  Lemma find_fptr_owner_determ
        mss fptr ms0 ms1
        (DISJ: SkEnv.disj ms0.(ModSem.skenv) ms1.(ModSem.skenv))
        (FIND0: find_fptr_owner mss fptr ms0)
        (FIND1: find_fptr_owner mss fptr ms1):
      ms0 = ms1.
  Proof.
    inv FIND0. inv FIND1. rr in DISJ. exploit DISJ; et. i; des. clarify.
  Qed.

  Require Import RelationClasses Morphisms.
  Require Import Relation_Operators.
  Require Import Relations.
  Local Open Scope signature_scope.

  Lemma ForallOrdPairs_map
        X Y (f: X -> Y) rx ry xs
        (DISJ: ForallOrdPairs rx xs)
        (RESPECTFUL: (rx ==> ry) f f)
    :
      <<DISJ: ForallOrdPairs ry (map f xs)>>
  .
  Proof.
    ginduction xs; ii; ss.
    { econs; et. }
    inv DISJ.
    econs; et.
    - rewrite Forall_forall in *. ii. rewrite in_map_iff in *. des. clarify. et.
    - eapply IHxs; et.
  Qed.

  Definition mod_disj (md0 md1: Mod.t): Prop := Sk.disj (Mod.sk md0) (Mod.sk md1).
  Definition modsem_disj (ms0 ms1: ModSem.t): Prop := SkEnv.disj (ModSem.skenv ms0) (ModSem.skenv ms1).
  Lemma modsem_respects_disj: forall skenv,
      (mod_disj ==> modsem_disj) (flip Mod.modsem skenv) (flip Mod.modsem skenv).
  Proof.
    ii. des. unfold Mod.modsem, flip in *. rewrite <- ! Mod.get_modsem_skenv_spec in *.
    eapply SkEnv.project_respects_disj; et.
  Qed.

  Lemma link_sk_disjoint
        p sk_link
        (LINK: link_sk p = Some sk_link)
    :
      <<DISJ: ForallOrdPairs mod_disj p>>
  .
  Proof.
    ginduction p; ii; ss.
    unfold link_sk in *. ss.
    destruct (classic (p = [])).
    { clarify; ss. econs; et. econs; et. }
    exploit link_list_cons_inv; et.
    { destruct p; ss. }
    i; des.
    exploit IHp; et. intro T; des.
    econs 2; et.
    rewrite Forall_forall. i. r.
    eapply Sk.link_disj in HD.
    eapply Sk.disj_linkorder; et. exploit link_list_linkorder; et. intro U; des.
    rewrite Forall_forall in *. eapply U. rewrite in_map_iff; et.
  Qed.

  Lemma find_fptr_owner_determ_link
        p sk_link skenv_link fptr ms0 ms1
        (LINK: link_sk p = Some sk_link)
        (LOAD: Sk.load_skenv sk_link = skenv_link)
        (FIND0: Ge.find_fptr_owner (load_genv p skenv_link) fptr ms0)
        (FIND1: Ge.find_fptr_owner (load_genv p skenv_link) fptr ms1)
    :
      ms0 = ms1.
  Proof.
    inv FIND0. inv FIND1.
    exploit link_sk_disjoint; et. intro T; des.
    set (skenv_link := (Sk.load_skenv sk_link)) in *.
    eapply (@ForallOrdPairs_map Mod.t ModSem.t (fun md => Mod.modsem md skenv_link)) in T; cycle 1.
    { eapply modsem_respects_disj; et. }
    assert(U: ForallOrdPairs modsem_disj (fst (load_genv p skenv_link))).
    { econs; et. rewrite Forall_forall.
      ii. ss. unfold System.skenv in *. eapply Genv.filter_map_funct_some in FINDF. des_safe. des_ifs.
      unfold load_modsems, flip, Mod.modsem in *. rewrite in_map_iff in *. des_safe. ss.
      rewrite <- Mod.get_modsem_skenv_spec in FINDF0.
      exploit SkEnv.project_linkorder; et.
    }
    clear T.
    exploit ForallOrdPairs_In; [|apply MODSEM|apply MODSEM0|..]; et. ii; des; clarify.
    - rr in H. exploit H; et. i; clarify.
    - rr in H. exploit H; et. i; clarify.
  Qed.

End AUX.

Section INITDTM.

  Context `{SM: SimMem.class}.
  Context {SS: SimSymb.class SM}.
  Variable p: program.
  Hypothesis (WFSK: forall md (IN: In md p), <<WF: Sk.wf md>>).
  Let sem := Sem.sem p.

  Lemma find_fptr_owner_determ
        fptr ms0 ms1
        (FIND0: Ge.find_fptr_owner sem.(globalenv) fptr ms0)
        (FIND1: Ge.find_fptr_owner sem.(globalenv) fptr ms1):
      ms0 = ms1.
  Proof.
    ss. des_ifs; cycle 1.
    { inv FIND0; ss. }
    eapply AUX.find_fptr_owner_determ_link; et.
  Qed.

  Theorem initial_state_determ
          st_init0 st_init1
          (INIT0: sem.(Smallstep.initial_state) st_init0)
          (INIT1: sem.(Smallstep.initial_state) st_init1):
      st_init0 = st_init1.
  Proof.
    ss. inv INIT0; inv INIT1; ss. clarify.
  Qed.

End INITDTM.




Lemma lift_step
      (ms: ModSem.t) st0 tr st1
      (STEP: Step ms st0 tr st1):
    forall prog tail,
    <<STEP: Step (Sem.sem prog)
                 (State ((Frame.mk ms st0) :: tail)) tr
                 (State ((Frame.mk ms st1) :: tail))>>.
Proof. ii. econs 3; eauto. Qed.

Lemma lift_star
      (ms: ModSem.t) st0 tr st1
      (STAR: Star ms st0 tr st1):
    forall prog tail,
    <<STAR: Star (Sem.sem prog) (State ((Frame.mk ms st0) :: tail)) tr (State ((Frame.mk ms st1) :: tail))>>.
Proof.
  ii. ginduction STAR; ii; ss.
  - econs 1; eauto.
  - clarify. econs 2; eauto.
    + eapply lift_step; eauto.
    + eapply IHSTAR; eauto.
Qed.

Lemma lift_plus
      (ms: ModSem.t) st0 tr st1
      (PLUS: Plus ms st0 tr st1):
    forall prog tail,
    <<PLUS: Plus (Sem.sem prog) (State ((Frame.mk ms st0) :: tail)) tr (State ((Frame.mk ms st1) :: tail))>>.
Proof.
  i. inv PLUS; ii; ss. econs; eauto.
  - eapply lift_step; eauto.
  - eapply lift_star; eauto.
Qed.

Lemma lift_dstep
      (ms: ModSem.t) st0 tr st1 prog
      (PUBEQ: ms.(symbolenv).(Senv.public_symbol) = (Sem.sem prog).(symbolenv).(Senv.public_symbol))
      (DSTEP: DStep ms st0 tr st1):
    forall tail,
    <<DSTEP: DStep (Sem.sem prog) (State ((Frame.mk ms st0) :: tail)) tr (State ((Frame.mk ms st1) :: tail))>>.
Proof.
  ii. destruct DSTEP as [DTM STEP]. econs; eauto; cycle 1.
  - econs; ss; eauto.
  - inv DTM. econs; eauto.
    + ii. ss. inv H; ss; ModSem.tac. inv H0; ss; ModSem.tac. clear STEP.
      determ_tac sd_determ_at. esplits; auto.
      * eapply match_traces_preserved; try apply H. i. s. congruence.
      * ii. clarify. special H0; ss. clarify.
    + ii. ss. inv STEP0; ss; ModSem.tac. inv FINAL; ss; ModSem.tac.
    + ii. inv H; ss; ModSem.tac. exploit sd_traces_at; eauto.
Qed.

Lemma lift_dstar
      (ms: ModSem.t) st0 tr st1 prog
      (PUBEQ: ms.(symbolenv).(Senv.public_symbol) = (Sem.sem prog).(symbolenv).(Senv.public_symbol))
      (DSTAR: DStar ms st0 tr st1):
    forall tail,
    <<DSTAR: DStar (Sem.sem prog) (State ((Frame.mk ms st0) :: tail)) tr (State ((Frame.mk ms st1) :: tail))>>.
Proof.
  i. ginduction DSTAR; ii; ss.
  - econs 1; eauto.
  - clarify. econs 2; eauto.
    + eapply lift_dstep; eauto.
    + eapply IHDSTAR; eauto.
Qed.

Lemma lift_dplus
      (ms: ModSem.t) st0 tr st1 prog
      (PUBEQ: ms.(symbolenv).(Senv.public_symbol) = (Sem.sem prog).(symbolenv).(Senv.public_symbol))
      (DPLUS: DPlus ms st0 tr st1):
    forall tail,
    <<DPLUS: DPlus (Sem.sem prog) (State ((Frame.mk ms st0) :: tail)) tr (State ((Frame.mk ms st1) :: tail))>>.
Proof.
  i. inv DPLUS; ii; ss. econs; eauto.
  - eapply lift_dstep; eauto.
  - eapply lift_dstar; eauto.
Qed.

Lemma lift_receptive_at
      (ms: ModSem.t) st0 prog
      (PUBEQ: ms.(symbolenv).(Senv.public_symbol) = (Sem.sem prog).(symbolenv).(Senv.public_symbol))
      (RECEP: receptive_at ms st0):
    forall tail, <<RECEP: receptive_at (Sem.sem prog) (State ((Frame.mk ms st0) :: tail))>>.
Proof.
  ii. inv RECEP. ss. econs; eauto; ii.
  - inv H.
    + eapply match_traces_nil_l in H0; subst. esplits; eauto. econs 1; eauto.
    + ss. exploit sr_receptive_at; eauto.
      { eapply match_traces_preserved; try apply H0. i. s. congruence. }
      i; des. esplits; eauto. econs; eauto.
    + eapply match_traces_nil_l in H0; subst. esplits; eauto. econs 4; eauto.
  - inv H; s; try omega. exploit sr_traces_at; eauto.
Qed.

Lemma lift_determinate_at
      (ms: ModSem.t) st0 prog
      (PUBEQ: ms.(symbolenv).(Senv.public_symbol) = (Sem.sem prog).(symbolenv).(Senv.public_symbol))
      (DTM: determinate_at ms st0):
    forall tail,
    <<DTM: determinate_at (Sem.sem prog) (State ((Frame.mk ms st0) :: tail))>>.
Proof.
  ii. inv DTM. ss. econs; eauto; ii.
  - inv H; inv H0; ModSem.tac.
    + esplits; et.
      { eapply match_traces_nil_nil; et. }
      i. f_equal. eapply ModSem.at_external_dtm; et.
    + ss. determ_tac sd_determ_at. esplits; et.
      { eapply match_traces_preserved; try apply H. i. s. congruence. }
      i. clarify. repeat f_equal. eauto.
    + ss. esplits; et.
      { eapply match_traces_nil_nil; et. }
      i. repeat f_equal. determ_tac ModSem.final_frame_dtm. eapply ModSem.after_external_dtm; et.
  - ss. inv FINAL. ss. inv STEP; ss; ModSem.tac.
  - inv H; s; try omega. exploit sd_traces_at; eauto.
Qed.

(* Lemma callstate_receptive_at *)
(*       prog *)
(*       args frs *)
(*   : *)
(*     <<RECEP: receptive_at (Sem.sem prog) (Callstate args frs)>> *)
(* . *)
(* Proof. *)
(*   econs; eauto. *)
(*   - ii. ss. des_ifs. *)
(*     + inv H. inv H0. esplits; eauto. econs; eauto. *)
(*     + inv H. inv MSFIND. ss. *)
(*   - ii. inv H. ss. omega. *)
(* Qed. *)

(* Lemma callstate_determinate_at *)
(*       prog *)
(*       args frs *)
(*   : *)
(*     <<RECEP: determinate_at (Sem.sem prog) (Callstate args frs)>> *)
(* . *)
(* Proof. *)
(*   econs; eauto. *)
(*   - ii. ss. des_ifs. *)
(*     + inv H. inv H0. esplits; eauto. *)
(*       * econs; eauto. *)
(*       * i. repeat f_equal. clear_tac. *)
(*         exploit find_fptr_owner_determ; eauto. *)
(*         { ss. rewrite Heq. eapply MSFIND. } *)
(*         { ss. rewrite Heq. eapply MSFIND0. } *)
(*         i; clarify. *)
(*         determ_tac ModSem.initial_frame_dtm. *)
(*     + exfalso. inv H. inv MSFIND. ss. *)
(*   - ii. ss. des_ifs. *)
(*     + inv FINAL. *)
(*     + inv FINAL. *)
(*   - ii. inv H. ss. omega. *)
(* Qed. *)

Section WFMEM.

  Lemma link_load_skenv_wf_mem
        p sk_link m_init
        (LINK: link_sk p = Some sk_link)
        (WF: forall md (IN: In md p), Sk.wf md)
        (LOADM: Sk.load_mem sk_link = Some m_init):
    let skenv_link := Sk.load_skenv sk_link in
    <<WFM: forall md (IN: In md p), SkEnv.wf_mem skenv_link md m_init>>.
  Proof.
    ii. eapply SkEnv.load_skenv_wf_mem; et.
    { eapply link_list_preserves_wf_sk; et. }
    { unfold link_sk in *. hexploit (link_list_linkorder _ LINK); et. intro T; des.
      rewrite Forall_forall in T. eapply T; et. rewrite in_map_iff. esplits; et. }
  Qed.

End WFMEM.


Require Import Sem SimModSem.
Theorem safe_implies_safe_modsem
        p sk ms lst tail
        (LINK: link_sk p = Some sk)
        (SAFE: safe (sem p) (State ({| Frame.ms := ms; Frame.st := lst |} :: tail))):
    <<SAFE: safe_modsem ms lst>>.
Proof.
  ii. ss. exploit SAFE.
  { instantiate (1:= (State ({| Frame.ms := ms; Frame.st := st1 |} :: tail))). eapply lift_star; eauto. }
  i; des.
  - ss. inv H. ss. right. left. eauto.
  - ss. des_ifs. inv H; ss.
    + left. eauto.
    + right. right. eauto.
    + right. left. eauto.
Qed.


Lemma backward_simulation_refl: forall SEM, backward_simulation SEM SEM.
Proof.
  i. eapply (@Backward_simulation _ _ unit bot2). econs; eauto.
  { apply unit_ord_wf. }
  ii. ss. exists tt. esplits; eauto.
  clear st_init_src_ INITSRC INITTGT. rename st_init_tgt into st. revert st.
  pcofix CIH. i. pfold. econs; eauto.
  ii. econs; eauto.
  { ii. esplits; eauto. left. apply plus_one. ss. }
  { i. r in SAFESRC. specialize (SAFESRC st (star_refl _ _ _ _)). ss. }
  { ii. esplits; eauto. econs; eauto. }
Qed.

Lemma sk_nwf_improves (mds_src mds_tgt: program)
      (NWF: ~ (forall x (IN: In x mds_src), Sk.wf x)):
      improves (sem mds_src) (sem mds_tgt).
Proof.
  eapply bsim_improves. econs. econs; try (i; inv INITSRC; clarify). eapply unit_ord_wf.
Qed.
