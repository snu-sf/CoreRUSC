Require Import CoqlibC.
Require Import List.
Require Import LinkingC.

Set Implicit Arguments.



Module AST.
  Class class: Type := {
    ident: Type;
    signature: Type;
    signature_main: signature;
    external_function: Type;
    ef_sig: external_function -> signature;
    globvar: Type -> Type
  }
  .

  Section AST.
    Context `{class}.
    Inductive fundef (F: Type): Type :=
    | Internal: F -> fundef F
    | External: external_function -> fundef F.

    Inductive globdef (F V : Type) : Type :=
    | Gfun : F -> globdef F V
    | Gvar : globvar V -> globdef F V
    .

  End AST.

End AST.
Export AST.

Arguments Internal {_} [_].
Arguments External {_} [_].
Arguments Gfun {_} [_] [_].
Arguments Gvar {_} [_] [_].

Module Values.
  Class class: Type := {
    val: Type;
    Vundef: val;
    int: Type;
    Vint: int -> val;
    Vint_inj: forall a b, Vint a = Vint b -> a = b;
  }
  .
End Values.
Export Values.

Module Asm.
  Class class `{Values.class}: Type := {
    regs: Type;
    PC: regs;
    regset := regs -> val;
  }
  .
End Asm.

Module Mem.
  Class class: Type := {
    t: Type;
    empty: t;
  }
  .
End Mem.
Definition mem `{Mem.class}: Type := Mem.t.

Module Senv.
  Class class `{AC: AST.class}: Type := {
    t: Type;
    public_symbol: t -> AST.ident -> bool;
  }
  .
End Senv.

Module Genv.
  Class class `{AST.class} `{Values.class} `{Senv.class}: Type := {
    t: Type -> Type -> Type;
    to_senv: forall {F V}, (t F V) -> Senv.t;
    find_funct: forall {F V}, (t F V) -> val -> option F;
    symbol_address: forall {F V}, (t F V) -> ident -> val;
    map_defs: forall {F1 V1 F2 V2}, (t F1 V1) -> (globdef F1 V1 -> option (globdef F2 V2)) -> (t F2 V2);
    public_symbol: forall {F V}, (t F V) -> AST.ident -> bool :=
      fun _ _ ge => Senv.public_symbol (to_senv ge);
    map_defs_find_funct: forall
        F1 V1 F2 V2
        ge (trans: globdef F1 V1 -> option (globdef F2 V2)) fptr fd0
        (FINDF: find_funct (map_defs ge trans) fptr = Some fd0)
      ,
        exists fd1, (<<FINDF: find_funct ge fptr = Some fd1>>) /\
                    (<<MAP: trans (Gfun fd1) = Some (Gfun fd0)>>)
    ;
    (* find_funct_some: forall *)
    (*     F V (ge: t F V) fptr fd *)
    (*     (FINDF: ge.(find_funct) fptr = Some fd) *)
    (*   , *)
    (*     (<<FPTR: fptr <> Vundef>>); *)
  }
  .
  
End Genv.
Coercion Genv.to_senv: Genv.t >-> Senv.t.

Module Sk.
  Class class `{Genv.class} `{AST.class} `{Mem.class}: Type := {
    t: Type;
    prog_main: t -> ident;
    wf: t -> Prop;
    Linker:> Linker t;
    load_skenv: t -> Genv.t (fundef signature) unit;
    load_mem: t -> option mem;
    link_preserves_wf_sk: forall
        sk0 sk1 sk_link
        (WFSK0: wf sk0)
        (WFSK1: wf sk1)
        (LINK: link sk0 sk1 = Some sk_link)
      ,
        (<<WF: wf sk_link>>)
    ;
    disj: t -> t -> Prop;
    link_disj: forall 
        sk0 sk1 sk_link
        (LINK: link sk0 sk1 = Some sk_link)
      ,
        (<<DISJ: disj sk0 sk1>>)
    ;
    disj_linkorder: forall
        sk0 sk1 sk_link
        (DISJ: disj sk0 sk_link)
        (LINK: linkorder sk1 sk_link)
      ,
        (<<DISJ: disj sk0 sk1>>)
    ;
  }
  .

End Sk.
Definition prog_main `{Sk.class} := Sk.prog_main.

Module SkEnv.
  (*** NOTE: put `{Genv.class} and you get an error, because there are multiple instances of Genv.class
             (one required by Sk.class and the other)
       TODO: Avoid such thing systematically?
   ***)
  Class class `{Sk.class}: Type := {
    t: Type := Genv.t (fundef signature) unit;
    wf: t -> Prop;
    wf_mem: t -> Sk.t -> mem -> Prop;
    to_senv: t -> Senv.t := Genv.to_senv;
    project: t -> Sk.t -> t;
    project_spec: t -> Sk.t -> t -> Prop;
    includes: t -> Sk.t -> Prop;
    project_impl_spec: forall skenv sk (INCL: includes skenv sk),
        (<<PROJ: project_spec skenv sk (project skenv sk)>>);
    linkorder_includes: forall
        (sk0 sk1: Sk.t)
        (LO: linkorder sk0 sk1)
      ,
        (<<INCL: includes (Sk.load_skenv sk1) sk0>>);
    empty: t;
    load_skenv_wf: forall
        sk
        (WF: Sk.wf sk)
      ,
        (<<WF: wf (Sk.load_skenv sk)>>)
    ;
    load_skenv_wf_mem: forall
        sk_link m_init
        (WF: Sk.wf sk_link)
        (LOADM: Sk.load_mem sk_link = Some m_init)
      ,
        let skenv_link := Sk.load_skenv sk_link in
        <<WFM: forall sk (WF: Sk.wf sk) (LO: linkorder sk sk_link), wf_mem skenv_link sk m_init>>
    ;
    disj (ske0 ske1: t): Prop := forall
      fptr f0 f1
      (FINDF: Genv.find_funct ske0 fptr = Some (Internal f0))
      (FINDF: Genv.find_funct ske1 fptr = Some (Internal f1))
    ,
      False;
    project_respects_disj: forall
        sk0 sk1 ske0 ske1 ske_link
        (DISJ: Sk.disj sk0 sk1)
        (LOAD0: project ske_link sk0 = ske0)
        (LOAD1: project ske_link sk1 = ske1)
      ,
        (<<DISJ: disj ske0 ske1>>)
    ;
    project_linkorder: forall
        skenv_link fptr sk ef fd
        (FINDF0: Genv.find_funct skenv_link fptr = Some (External ef))
        (FINDF1: Genv.find_funct (project skenv_link sk) fptr = Some (Internal fd))
      ,
        False
    ;
  }
  .

End SkEnv.

Coercion SkEnv.to_senv: SkEnv.t >-> Senv.t.

Module Events.
  Class class `{VC: Values.class} `{MC: Mem.class} `{SC: Senv.class}: Type := {
    event: Type;
    trace := list event;
    Eapp: trace -> trace -> trace := @app _;
    E0: trace := nil;
    match_traces: Senv.t -> trace -> trace -> Prop;
    match_traces_nil_nil: forall se, match_traces se E0 E0;
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



(****************************************************************************************)
(****************************************************************************************)
(****************************************************************************************)
(****************************************************************************************)
(****************************************************************************************)

Class UNIVERSE: Type := {
  Mem_class:> Mem.class;
  Values_class:> Values.class;
  Asm_class:> Asm.class;
  AST_class:> AST.class;
  Senv_class:> Senv.class;
  Genv_class:> Genv.class;
  Events_class:> Events.class;
  Sk_class:> Sk.class;
  SkEnv_class:> SkEnv.class;
}
.

Context {UN: UNIVERSE}.

(****************************************************************************************)
(****************************************************************************************)
(****************************************************************************************)
(****************************************************************************************)
(****************************************************************************************)

