Require Import sflib.
Require Import List.

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

Module Senv.
  Class class `{AST.class}: Type := {
    t: Type;
    public_symbol: t -> AST.ident -> bool;
  }
  .
End Senv.

Module Genv.
  Class class `{Senv.class}: Type := {
    t: Type -> Type -> Type;
    to_senv: forall {F V}, (t F V) -> Senv.t;
  }
  .
End Genv.
Coercion Genv.to_senv: Genv.t >-> Senv.t.

Export AST.

Module SkEnv.
  Section SkEnv.
    Context `{Genv.class}.
    Definition t: Type := Genv.t (fundef signature) unit.
    Definition to_senv: SkEnv.t -> Senv.t := Genv.to_senv.
  End SkEnv.
End SkEnv.

Coercion SkEnv.to_senv: SkEnv.t >-> Senv.t.

Module Events.
  Class class `{Senv.class}: Type := {
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
  }
  .
End Events.

Export Events.

Module Mem.
  Class class: Type := {
    t: Type;
    empty: t;
  }
  .
End Mem.





Class PARAMETERS: Type := {
  Mem_class:> Mem.class;
  AST_class:> AST.class;
  Senv_class:> Senv.class;
  Genv_class:> Genv.class;
  Events_class:> Events.class;
  val: Type;
  Vundef: val;
  regs: Type;
  PC: regs;
  mem := Mem.t;
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
