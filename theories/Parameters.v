Require Import sflib.
Require Import List.
Require Import LinkingC.

Set Implicit Arguments.



Module AST.
  Class class: Type := {
    ident: Type;
    signature: Type;
    external_function: Type;
  }
  .

  Section AST.
    Context `{class}.
    Inductive fundef (F: Type): Type :=
    | Internal: F -> fundef F
    | External: external_function -> fundef F.
  End AST.

End AST.

Module Values.
  Class class: Type := {
    val: Type;
    Vundef: val;
  }
  .
End Values.

Export Values.

Module Mem.
  Class class: Type := {
    t: Type;
    empty: t;
  }
  .
End Mem.
Definition mem `{Mem.class}: Type := Mem.t.

Module Senv.
  Class class `{AST.class}: Type := {
    t: Type;
    public_symbol: t -> AST.ident -> bool;
  }
  .
End Senv.

Module Genv.
  Class class `{Values.class} `{Senv.class}: Type := {
    t: Type -> Type -> Type;
    to_senv: forall {F V}, (t F V) -> Senv.t;
    find_funct: forall {F V}, (t F V) -> val -> option F;
  }
  .
End Genv.
Coercion Genv.to_senv: Genv.t >-> Senv.t.

Export AST.

Module Sk.
  Class class: Type := {
    t: Type;
    Linker:> Linker t;
  }
  .
End Sk.

Module SkEnv.
  Class class `{Sk.class} `{Genv.class}: Type := {
    t: Type := Genv.t (fundef signature) unit;
    to_senv: t -> Senv.t := Genv.to_senv;
    project: t -> Sk.t -> t;
    project_spec: t -> Sk.t -> t -> Prop;
    includes: t -> Sk.t -> Prop;
    project_impl_spec: forall skenv sk (INCL: includes skenv sk),
        <<PROJ: project_spec skenv sk (project skenv sk)>>
  }
  .
End SkEnv.

Coercion SkEnv.to_senv: SkEnv.t >-> Senv.t.

Module Events.
  Class class `{Values.class} `{Mem.class} `{Senv.class}: Type := {
    event: Type;
    trace := list event;
    Eapp: trace -> trace -> trace := @app _;
    E0: trace := nil;
    match_traces: Senv.t -> trace -> trace -> Prop;
    match_traces_nil_l: forall
        se t
        (MATCH: match_traces se E0 t)
      ,
        t = E0;
    match_traces_nil_r: forall
        se t
        (MATCH: match_traces se t E0)
      ,
        t = E0;
    match_traces_preserved: forall
        ge1 ge2
        (PUBS: forall id, ge2.(Senv.public_symbol) id = ge1.(Senv.public_symbol) id)
      ,
        forall t1 t2, match_traces ge1 t1 t2 -> match_traces ge2 t1 t2
    ;
    extcall_sem := Senv.t -> list val -> mem -> trace -> val -> mem -> Prop;
    external_call: external_function -> extcall_sem;
    external_call_receptive: forall (sem: extcall_sem) ge vargs m t1 vres1 m1 t2,
        sem ge vargs m t1 vres1 m1 -> match_traces ge t1 t2 ->
        exists vres2, exists m2, sem ge vargs m t2 vres2 m2;
    external_call_deterministic: forall (sem: extcall_sem) ge vargs m t1 vres1 m1 t2 vres2 m2,
        sem ge vargs m t1 vres1 m1 -> sem ge vargs m t2 vres2 m2 ->
        match_traces ge t1 t2 /\ (t1 = t2 -> vres1 = vres2 /\ m1 = m2);
    external_call_trace_length: forall (sem: extcall_sem) ge vargs m t vres m',
        sem ge vargs m t vres m' -> (length t <= 1)%nat;
    external_call_match_traces: forall ef ge vargs m t1 vres1 m1 t2 vres2 m2,
        external_call ef ge vargs m t1 vres1 m1 ->
        external_call ef ge vargs m t2 vres2 m2 ->
        match_traces ge t1 t2;
  }
  .
End Events.

Export Events.






Class PARAMETERS: Type := {
  Mem_class:> Mem.class;
  Values_class:> Values.class;
  AST_class:> AST.class;
  Senv_class:> Senv.class;
  Genv_class:> Genv.class;
  Events_class:> Events.class;
  Sk_class:> Sk.class;
  SkEnv_class:> SkEnv.class;
  regs: Type;
  PC: regs;
  regset := regs -> val;
  int: Type;
}
.

Context {PRMS: PARAMETERS}.

Check Mem.empty.
Check Senv.t.



Infix "**" := Eapp (at level 60, right associativity).

Lemma E0_left: forall t, E0 ** t = t.
Proof. auto. Qed.

Lemma E0_right: forall t, t ** E0 = t.
Proof. intros. unfold E0, Eapp. rewrite <- app_nil_end. auto. Qed.

Lemma Eapp_assoc: forall t1 t2 t3, (t1 ** t2) ** t3 = t1 ** (t2 ** t3).
Proof. intros. unfold Eapp, trace. apply app_ass. Qed.

Lemma Eapp_E0_inv: forall t1 t2, t1 ** t2 = E0 -> t1 = E0 /\ t2 = E0.
Proof (@app_eq_nil event).

(* Lemma E0_left_inf: forall T, E0 *** T = T. *)
(* Proof. auto. Qed. *)

(* Lemma Eappinf_assoc: forall t1 t2 T, (t1 ** t2) *** T = t1 *** (t2 *** T). *)
(* Proof. *)
(*   induction t1; intros; simpl. auto. decEq; auto. *)
(* Qed. *)

Hint Rewrite E0_left E0_right Eapp_assoc
             (* E0_left_inf Eappinf_assoc *)
  : trace_rewrite.

Ltac substTraceHyp :=
  match goal with
  | [ H: (@eq trace ?x ?y) |- _ ] =>
       subst x || clear H
  end.

Ltac decomposeTraceEq :=
  match goal with
  | [ |- (_ ** _) = (_ ** _) ] =>
      apply (f_equal2 app); auto; decomposeTraceEq
  | _ =>
      auto
  end.

Ltac traceEq :=
  repeat substTraceHyp; autorewrite with trace_rewrite; decomposeTraceEq.
