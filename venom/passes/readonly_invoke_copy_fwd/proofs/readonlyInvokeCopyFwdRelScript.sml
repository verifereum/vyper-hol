(* Relocation at the RICF call boundary.  Site keys are source provenance
   (base,size), not target addresses: distinct keys may share a target. *)
Theory readonlyInvokeCopyFwdRel
Ancestors
  internalReturnCopyFwdSim o1LowerDloadRelocationKernel reachableFnSim
  taintAgree o1LowerDloadShared ptrDiscipline codegenRel
  venomExecSemantics venomState finite_map words list rich_list pred_set

(* Keep the existing relocation kernel's value algebra.  A provenance
   without an active translation is an ordinary (possibly tainted) value. *)
Definition ricf_value_agree_def:
  ricf_value_agree sites p m x y <=>
    ld_value_agree sites
      (case p of NONE => NONE
       | SOME id => if id IN FDOM sites then SOME id else NONE) m x y /\
    (!id. p = SOME id /\ id IN FDOM sites ==> m = {})
End

Definition ricf_sites_ok_def:
  ricf_sites_ok sites <=>
    !db sz b c z. FLOOKUP sites (db,sz) = SOME (b,c,z) ==>
                 b = db /\ z = sz
End

Definition ricf_site_triples_def:
  ricf_site_triples sites = {tr | ?id. FLOOKUP sites id = SOME tr}
End

Definition ricf_params_agree_def:
  ricf_params_agree sites PG xs ys <=>
    LENGTH xs = LENGTH ys /\ LENGTH PG = LENGTH xs /\
    (!j. j < LENGTH xs ==>
      ricf_value_agree sites (EL j PG) {} (EL j xs) (EL j ys))
End

(* Normalizing only the two relocated fields lets taint_agree retain
   ownership of all the shared-state and frame-field obligations. *)
Definition ricf_frame_agree_def:
  ricf_frame_agree D X sites PG G tn s t <=>
    taint_agree D X tn s
      (t with <| vs_vars := s.vs_vars; vs_params := s.vs_params |>) /\
    FDOM t.vs_vars = FDOM s.vs_vars /\
    (!v. v IN FDOM s.vs_vars ==>
      ricf_value_agree sites (FLOOKUP G v) (op_taint tn (Var v))
        (s.vs_vars ' v) (t.vs_vars ' v)) /\
    ricf_params_agree sites PG s.vs_params t.vs_params /\
    ricf_sites_ok sites /\
    ircf_cross tn (ricf_site_triples sites) s t
End

(* Explicit ghosts for suspended frames.  No injectivity condition is
   imposed on the sites maps, and inherited sites can be retained at
   arbitrary call depth. *)
Definition ricf_stack_agree_def:
  ricf_stack_agree D ids tn maps stk targets <=>
    LENGTH maps = LENGTH stk /\ LENGTH targets = LENGTH stk /\
    (!j. j < LENGTH stk ==>
      ricf_frame_agree D
        (ircf_dead ids (EL j stk).cf_state (DROP (SUC j) stk))
        (EL j maps) (EL j stk).cf_params (EL j stk).cf_prov
        (tn with t_var := (EL j stk).cf_tvar)
        (EL j stk).cf_state (EL j targets))
End

Theorem ricf_value_agree_empty:
  ricf_value_agree FEMPTY p m x y <=> word_agree_except m x y
Proof
  Cases_on `p` >> simp[ricf_value_agree_def, ld_value_agree_def]
QED

Theorem ricf_value_agree_relocated:
  ricf_sites_ok sites /\ FLOOKUP sites (db,sz) = SOME (db,sb,sz) ==>
  (ricf_value_agree sites (SOME (db,sz)) m x y <=>
   m = {} /\ y = x + n2w sb - n2w db)
Proof
  simp[ricf_value_agree_def, ld_value_agree_def, FLOOKUP_DEF] >>
  metis_tac[]
QED

Theorem ricf_params_agree_empty:
  LENGTH PG = LENGTH xs ==> ricf_params_agree FEMPTY PG xs xs
Proof
  simp[ricf_params_agree_def, ricf_value_agree_empty, word_agree_except_def]
QED

Theorem ricf_frame_agree_identity:
  taint_agree D X tn s s /\ LENGTH PG = LENGTH s.vs_params ==>
  ricf_frame_agree D X FEMPTY PG G tn s s
Proof
  simp[ricf_frame_agree_def, ricf_value_agree_empty,
       ricf_params_agree_empty, ricf_sites_ok_def,
       ricf_site_triples_def, ircf_cross_def, word_agree_except_def]
QED

(* Finite reads transport byte taint as well as clean bytes.  This is
   deliberately not equality of reads when some bytes are tainted. *)
Theorem ricf_cross_finite_read:
  ircf_cross tn gam s t /\ (db,sb,sz) IN gam /\ off + len <= sz ==>
  LIST_REL (\i j. (i IN tn.t_mem <=> j IN tn.t_mem) /\
                  (i NOTIN tn.t_mem ==>
                   read_byte i s.vs_memory = read_byte j t.vs_memory))
    (GENLIST (\k. db + (off+k)) len)
    (GENLIST (\k. sb + (off+k)) len)
Proof
  strip_tac >> simp[LIST_REL_EL_EQN] >> gen_tac >> strip_tac >>
  fs[ircf_cross_def] >>
  first_x_assum (qspecl_then [`db`, `sb`, `sz`, `off+n`] mp_tac) >>
  impl_tac >- (simp[] >> decide_tac) >>
  simp[]
QED

(* Parameter entry needs equal return-PC tokens, not merely relocated
   argument values: setup_callee also saves LAST args in a scalar field. *)
Theorem ricf_setup_callee_params:
  setup_callee fn args s = SOME cs /\
  setup_callee fn args' t = SOME ct /\
  ricf_params_agree sites PG args args' ==>
  ricf_params_agree sites PG cs.vs_params ct.vs_params
Proof
  simp[setup_callee_def] >> IF_CASES_TAC >> simp[] >>
  rpt strip_tac >> gvs[]
QED

Theorem ricf_setup_callee_cross:
  setup_callee fn args s = SOME cs /\
  setup_callee fn args' t = SOME ct /\ ircf_cross tn gam s t ==>
  ircf_cross (tn with t_var := FEMPTY) gam cs ct
Proof
  simp[setup_callee_def] >> IF_CASES_TAC >> simp[] >>
  rpt strip_tac >> gvs[ircf_cross_def] >> gvs[]
QED

Theorem ricf_setup_callee_frame:
  ricf_frame_agree D X oldsites oldPG G tn s t /\
  ricf_params_agree sites PG args args' /\ ricf_sites_ok sites /\
  ircf_cross tn (ricf_site_triples sites) s t /\
  (if NULL args then 0w else LAST args) =
    (if NULL args' then 0w else LAST args') /\
  setup_callee fn args s = SOME cs /\
  setup_callee fn args' t = SOME ct ==>
  ricf_frame_agree D X sites PG FEMPTY (tn with t_var := FEMPTY) cs ct
Proof
  Cases_on `NULL fn.fn_blocks` >> simp[setup_callee_def] >>
  rpt strip_tac >> gvs[] >>
  fs[ricf_frame_agree_def, taint_agree_def, ld_shared_agree_def,
     ricf_value_agree_def, ld_value_agree_def, word_agree_except_def,
     ircf_cross_def] >> gvs[] >>
  reverse conj_tac >- metis_tac[] >>
  qpat_x_assum `_ = s` mp_tac >>
  simp[Once venom_state_component_equality] >> rpt strip_tac >>
  simp[venom_state_component_equality]
QED

(* The relation has exactly the ghost signature consumed by reachableFnSim.
   Copies executed in this frame and inherited translations are separate
   witnesses.  A translation already inherited can simply be retained at
   the next INVOKE; no target reachability/discipline premise is used. *)
Definition ricf_boundary_agree_def:
  ricf_boundary_agree D ids stk PG G tn fn s t <=>
    ?cur inherited sites maps targets G0 tn0.
      sites = FUNION cur inherited /\
      G = (if s.vs_prev_bb = NONE then G0 else entry_prov fn s G0) /\
      tn = (if s.vs_prev_bb = NONE then tn0 else entry_taint_vars fn s tn0) /\
      ricf_frame_agree D (ircf_dead ids s stk) sites PG G0 tn0 s t /\
      ricf_stack_agree D ids tn0 maps stk targets /\
      ircf_cross tn (ricf_site_triples cur UNION ricf_site_triples inherited) s t
End

Theorem ricf_params_agree_repeat:
  ricf_value_agree sites p {} x y ==>
  ricf_params_agree sites [p;p;NONE] [x;x;0w] [y;y;0w]
Proof
  simp[ricf_params_agree_def, ricf_value_agree_def, ld_value_agree_def,
       word_agree_except_def] >> rpt strip_tac >>
  `j = 0 \/ j = 1 \/ j = 2` by decide_tac >> gvs[]
QED

(* Two source destinations share a target; identity of the target site is
   not an injectivity constraint on provenance. *)
Theorem ricf_shared_target_probe:
  let sites = FEMPTY |+ ((64,32),(64,0,32)) |+ ((96,32),(96,0,32)) in
  ricf_sites_ok sites /\
  ricf_params_agree sites [SOME (64,32); SOME (96,32); NONE]
    [64w;96w;0w] [0w;0w;0w]
Proof
  simp_tac bool_ss [LET_THM] >> conj_tac
  >- (rw[ricf_sites_ok_def, FLOOKUP_UPDATE] >>
      gvs[AllCaseEqs()]) >>
  simp[ricf_params_agree_def] >> rpt strip_tac >>
  `j = 0 \/ j = 1 \/ j = 2` by decide_tac >>
  gvs[ricf_value_agree_def, ld_value_agree_def, FLOOKUP_UPDATE,
      word_agree_except_def] >> MATCH_ACCEPT_TAC WORD_ADD_SUB2
QED

(* Nested calls retain the same source key and the same target base,
   rather than applying the offset a second time. *)
Theorem ricf_nested_params_probe:
  setup_callee fn args s = SOME cs /\
  setup_callee fn args' t = SOME ct /\
  setup_callee inner args cs = SOME ds /\
  setup_callee inner args' ct = SOME dt /\
  ricf_params_agree inherited PG args args' ==>
  ricf_params_agree inherited PG ds.vs_params dt.vs_params
Proof
  metis_tac[ricf_setup_callee_params]
QED

(* PG is empty at context entry even when the initial parameter vector is
   not.  Complete only its missing provenance entries with scalar NONE. *)
Definition ricf_complete_params_def:
  ricf_complete_params PG xs =
    PG ++ REPLICATE (LENGTH xs - LENGTH PG) NONE
End

Definition ricf_entry_boundary_agree_def:
  ricf_entry_boundary_agree D ids stk PG G tn fn s t <=>
    ricf_boundary_agree D ids stk (ricf_complete_params PG s.vs_params)
      G tn fn s t
End

Theorem ricf_complete_params_length:
  LENGTH PG <= LENGTH xs ==>
  LENGTH (ricf_complete_params PG xs) = LENGTH xs
Proof
  simp[ricf_complete_params_def]
QED

Theorem ricf_complete_params_el:
  LENGTH PG <= LENGTH xs /\ j < LENGTH xs ==>
  EL j (ricf_complete_params PG xs) =
    if j < LENGTH PG then EL j PG else NONE
Proof
  simp[ricf_complete_params_def, EL_APPEND_EQN] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[EL_REPLICATE]
QED

Theorem ricf_frame_agree_completed_identity:
  taint_agree D X tn s s /\ LENGTH PG <= LENGTH s.vs_params ==>
  ricf_frame_agree D X FEMPTY (ricf_complete_params PG s.vs_params) G tn s s
Proof
  strip_tac >> irule ricf_frame_agree_identity >>
  simp[ricf_complete_params_length]
QED

Theorem ricf_entry_boundary_identity:
  s.vs_prev_bb = NONE /\ taint_agree D (ircf_dead ids s []) tn s s ==>
  ricf_entry_boundary_agree D ids [] [] FEMPTY tn fn s s
Proof
  strip_tac >>
  simp[ricf_entry_boundary_agree_def, ricf_boundary_agree_def] >>
  qexistsl [`FEMPTY`, `FEMPTY`, `[]`, `[]`] >>
  simp[ricf_stack_agree_def, ricf_site_triples_def, ircf_cross_def,
       ricf_frame_agree_completed_identity]
QED

(* Saved locals are compared without observing either saved memory. *)
Definition ricf_live_local_agree_def:
  ricf_live_local_agree sites PG G tv s t <=>
    merge_callee_state
      (t with <| vs_vars := s.vs_vars; vs_params := s.vs_params |>) s = s /\
    FDOM t.vs_vars = FDOM s.vs_vars /\
    (!v. v IN FDOM s.vs_vars ==>
      ricf_value_agree sites (FLOOKUP G v)
        (case FLOOKUP tv v of NONE => {} | SOME m => m)
        (s.vs_vars ' v) (t.vs_vars ' v)) /\
    ricf_params_agree sites PG s.vs_params t.vs_params /\
    ricf_sites_ok sites
End

Definition ricf_live_stack_agree_def:
  ricf_live_stack_agree D ids tn maps stk targets s t <=>
    LENGTH maps = LENGTH stk /\ LENGTH targets = LENGTH stk /\
    (!j. j < LENGTH stk ==>
      ricf_frame_agree D
        (ircf_dead ids (EL j stk).cf_state (DROP (SUC j) stk))
        (EL j maps)
        (ricf_complete_params (EL j stk).cf_params (EL j stk).cf_state.vs_params)
        (EL j stk).cf_prov (tn with t_var := (EL j stk).cf_tvar)
        (merge_callee_state (EL j stk).cf_state s)
        (merge_callee_state (EL j targets) t))
End

Theorem ricf_live_frame_decompose:
  ricf_frame_agree D X sites PG G (tn with t_var := tv)
    (merge_callee_state a s) (merge_callee_state b t) <=>
  ricf_live_local_agree sites PG G tv a b /\
  ld_shared_agree D a.vs_call_ctx.cc_address tn s t /\
  s.vs_returndata = t.vs_returndata /\
  (!i. i NOTIN X /\ i NOTIN tn.t_mem /\ i < a.vs_alloca_next ==>
       read_byte i s.vs_memory = read_byte i t.vs_memory) /\
  ircf_cross tn (ricf_site_triples sites) s t
Proof
  simp[ricf_frame_agree_def, ricf_live_local_agree_def,
       taint_agree_def, merge_callee_state_def, ld_shared_agree_def,
       ircf_cross_def, op_taint_def, venom_state_component_equality,
       word_agree_except_def] >>
  eq_tac >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ricf_live_stack_empty[simp]:
  ricf_live_stack_agree D ids tn [] [] [] s t
Proof
  simp[ricf_live_stack_agree_def]
QED

(* This is also an elimination rule for a particular ACTUAL saved target
   caller: choose j, then rewrite its EL equality. No fresh target state is
   introduced by this rule. *)
Theorem ricf_live_stack_frame:
  ricf_live_stack_agree D ids tn maps stk targets s t /\ j < LENGTH stk ==>
  ricf_live_local_agree (EL j maps)
    (ricf_complete_params (EL j stk).cf_params (EL j stk).cf_state.vs_params)
    (EL j stk).cf_prov (EL j stk).cf_tvar
    (EL j stk).cf_state (EL j targets) /\
  ld_shared_agree D (EL j stk).cf_state.vs_call_ctx.cc_address tn s t /\
  s.vs_returndata = t.vs_returndata /\
  (!i. i NOTIN ircf_dead ids (EL j stk).cf_state (DROP (SUC j) stk) /\
       i NOTIN tn.t_mem /\ i < (EL j stk).cf_state.vs_alloca_next ==>
       read_byte i s.vs_memory = read_byte i t.vs_memory) /\
  ircf_cross tn (ricf_site_triples (EL j maps)) s t
Proof
  simp[ricf_live_stack_agree_def, ricf_live_frame_decompose] >> metis_tac[]
QED

Theorem ricf_live_stack_cons:
  ricf_live_stack_agree D ids tn (sites::maps) (cf::stk) (target::targets) s t <=>
  ricf_frame_agree D (ircf_dead ids cf.cf_state stk) sites
    (ricf_complete_params cf.cf_params cf.cf_state.vs_params)
    cf.cf_prov (tn with t_var := cf.cf_tvar)
    (merge_callee_state cf.cf_state s) (merge_callee_state target t) /\
  ricf_live_stack_agree D ids tn maps stk targets s t
Proof
  simp[ricf_live_stack_agree_def] >> eq_tac
  >- (strip_tac >> conj_tac
      >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
      simp[] >> gen_tac >> strip_tac >>
      first_x_assum (qspec_then `SUC j` mp_tac) >> simp[]) >>
  strip_tac >> simp[] >> Cases >> simp[]
QED

(* Updates may change memory taint completely. Only local variable taint is
   saved; all memory and cross obligations below refer to the NEW states. *)
Theorem ricf_live_stack_refresh:
  ricf_live_stack_agree D ids tn maps stk targets s t /\
  (!j. j < LENGTH stk ==>
    ld_shared_agree D (EL j stk).cf_state.vs_call_ctx.cc_address un u v /\
    u.vs_returndata = v.vs_returndata /\
    (!i. i NOTIN ircf_dead ids (EL j stk).cf_state (DROP (SUC j) stk) /\
         i NOTIN un.t_mem /\ i < (EL j stk).cf_state.vs_alloca_next ==>
         read_byte i u.vs_memory = read_byte i v.vs_memory) /\
    ircf_cross un (ricf_site_triples (EL j maps)) u v) ==>
  ricf_live_stack_agree D ids un maps stk targets u v
Proof
  simp[ricf_live_stack_agree_def, ricf_live_frame_decompose] >>
  metis_tac[]
QED

Definition ricf_live_boundary_core_def:
  ricf_live_boundary_core D ids stk PG G tn fn sites maps targets G0 tn0 s t <=>
    G = (if s.vs_prev_bb = NONE then G0 else entry_prov fn s G0) /\
    tn = (if s.vs_prev_bb = NONE then tn0 else entry_taint_vars fn s tn0) /\
    ricf_frame_agree D (ircf_dead ids s stk) sites
      (ricf_complete_params PG s.vs_params) G0 tn0 s t /\
    ricf_live_stack_agree D ids tn0 maps stk targets s t
End

Definition ricf_live_boundary_agree_def:
  ricf_live_boundary_agree D ids stk PG G tn fn s t <=>
    ?sites maps targets G0 tn0.
      ricf_live_boundary_core D ids stk PG G tn fn
        sites maps targets G0 tn0 s t
End

(* The return core intentionally says nothing about current callee locals.
   Saved target locals remain explicitly indexed by the SAME targets list.
   merge/adopt/bind restoration is a separate semantic obligation. *)
Definition ricf_live_return_core_def:
  ricf_live_return_core D ids stk maps targets tn s t <=>
    ricf_live_stack_agree D ids tn maps stk targets s t /\
    ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
    s.vs_returndata = t.vs_returndata
End

Definition ricf_live_return_agree_def:
  ricf_live_return_agree D ids stk (PG:(num # num) option list)
      (G:(string,num # num) fmap) tn (fn:ir_function) (ret:internal_return) s t <=>
    ?maps targets. ricf_live_return_core D ids stk maps targets tn s t
End

Theorem ricf_live_boundary_identity:
  s.vs_prev_bb = NONE /\ taint_agree D (ircf_dead ids s []) tn s s ==>
  ricf_live_boundary_agree D ids [] [] FEMPTY tn fn s s
Proof
  strip_tac >>
  simp[ricf_live_boundary_agree_def, ricf_live_boundary_core_def] >>
  qexistsl [`FEMPTY`, `[]`, `[]`] >>
  simp[ricf_frame_agree_completed_identity]
QED

Theorem ricf_live_stack_setup:
  ricf_live_stack_agree D ids tn maps stk targets s t /\
  setup_callee fn args s = SOME cs /\
  setup_callee fn args' t = SOME ct ==>
  ricf_live_stack_agree D ids (tn with t_var := FEMPTY)
    maps stk targets cs ct
Proof
  simp[setup_callee_def] >> IF_CASES_TAC >> simp[] >>
  rpt strip_tac >> gvs[ricf_live_stack_agree_def,
    ricf_live_frame_decompose, ld_shared_agree_def, ircf_cross_def] >>
  metis_tac[]
QED

Theorem ricf_live_return_actual_caller:
  ricf_live_return_core D ids (cf::stk) (sites::maps)
    (caller::targets) tn s t ==>
  ricf_frame_agree D (ircf_dead ids cf.cf_state stk) sites
    (ricf_complete_params cf.cf_params cf.cf_state.vs_params)
    cf.cf_prov (tn with t_var := cf.cf_tvar)
    (merge_callee_state cf.cf_state s) (merge_callee_state caller t)
Proof
  simp[ricf_live_return_core_def, ricf_live_stack_cons]
QED

(* The fn_run_rel adapter is type-checked against the real internal_return
   result, rather than a stand-in value vector. *)
Theorem ricf_live_fn_run_return:
  ricf_live_return_core D ids stk maps targets tn s t ==>
  fn_run_rel D (ricf_live_return_agree D ids) stk PG fn
    (IntRet ret s) (IntRet ret t)
Proof
  simp[fn_run_rel_def, ricf_live_return_agree_def] >>
  metis_tac[]
QED

(* Historical memories may disagree at k. Both before and after clearing
   current memory taint, only the common LIVE memory u is compared. *)
Theorem ricf_live_taint_clearing_probe:
  cf.cf_state = a /\ LENGTH cf.cf_params <= LENGTH a.vs_params /\
  read_byte k a.vs_memory <> read_byte k oldmem ==>
  read_byte k cf.cf_state.vs_memory <>
    read_byte k (a with vs_memory := oldmem).vs_memory /\
  ricf_live_stack_agree D ids (tn with t_mem := {k})
    [FEMPTY] [cf] [a with vs_memory := oldmem] u u /\
  ricf_live_stack_agree D ids (tn with t_mem := {})
    [FEMPTY] [cf] [a with vs_memory := oldmem] u u
Proof
  strip_tac >> simp[] >>
  simp[ricf_live_stack_cons, ricf_live_frame_decompose,
    ricf_live_local_agree_def, merge_callee_state_def,
    ricf_value_agree_empty, word_agree_except_def,
    ricf_params_agree_empty, ricf_complete_params_length,
    ricf_sites_ok_def, ricf_site_triples_def, ircf_cross_def,
    ld_shared_agree_refl]
QED

(* Re-anchor a returned witness to the target caller that was actually
   saved at INVOKE. Only its saved LOCAL facts are required: none of the
   post-call memory facts are assumed again, nor a restored relation. *)
Theorem ricf_live_stack_reanchor:
  ricf_live_stack_agree D ids tn maps stk targets s t /\
  LENGTH actual = LENGTH stk /\
  (!j. j < LENGTH stk ==>
    ricf_live_local_agree (EL j maps)
      (ricf_complete_params (EL j stk).cf_params (EL j stk).cf_state.vs_params)
      (EL j stk).cf_prov (EL j stk).cf_tvar
      (EL j stk).cf_state (EL j actual)) ==>
  ricf_live_stack_agree D ids tn maps stk actual s t
Proof
  simp[ricf_live_stack_agree_def, ricf_live_frame_decompose] >> metis_tac[]
QED

Theorem ricf_live_return_reanchor:
  ricf_live_return_core D ids stk maps targets tn s t /\
  LENGTH actual = LENGTH stk /\
  (!j. j < LENGTH stk ==>
    ricf_live_local_agree (EL j maps)
      (ricf_complete_params (EL j stk).cf_params (EL j stk).cf_state.vs_params)
      (EL j stk).cf_prov (EL j stk).cf_tvar
      (EL j stk).cf_state (EL j actual)) ==>
  ricf_live_return_core D ids stk maps actual tn s t
Proof
  simp[ricf_live_return_core_def] >> metis_tac[ricf_live_stack_reanchor]
QED

Theorem ricf_live_save_caller:
  ricf_frame_agree D X sites PG G tn s t /\
  setup_callee fn args s = SOME cs /\
  setup_callee fn args' t = SOME ct ==>
  ricf_frame_agree D X sites PG G tn
    (merge_callee_state s cs) (merge_callee_state t ct)
Proof
  simp[setup_callee_def] >> IF_CASES_TAC >> simp[] >>
  rpt strip_tac >> gvs[merge_callee_state_def]
QED

Theorem ricf_live_nested_push:
  ricf_frame_agree D (ircf_dead ids s stk) sites
    (ricf_complete_params PG s.vs_params) G tn s t /\
  ricf_live_stack_agree D ids tn maps stk targets s t /\
  cf.cf_state = s /\ cf.cf_params = PG /\ cf.cf_prov = G /\
  cf.cf_tvar = tn.t_var /\
  setup_callee fn args s = SOME cs /\
  setup_callee fn args' t = SOME ct ==>
  ricf_live_stack_agree D ids (tn with t_var := FEMPTY)
    (sites::maps) (cf::stk) (t::targets) cs ct
Proof
  strip_tac >> simp[ricf_live_stack_cons] >> conj_tac
  >- (irule ricf_live_save_caller >> metis_tac[]) >>
  metis_tac[ricf_live_stack_setup]
QED

Theorem ricf_live_callee_dead:
  setup_callee fn args s = SOME cs /\ cf.cf_state = s ==>
  ircf_dead ids cs (cf::stk) = ircf_dead ids s stk
Proof
  simp[setup_callee_def] >> IF_CASES_TAC >> simp[] >>
  rpt strip_tac >> gvs[ircf_dead_def, site_bytes_def] >>
  simp[EXTENSION] >> metis_tac[]
QED

Theorem ricf_live_nested_entry:
  ricf_frame_agree D (ircf_dead ids s stk) oldsites
    (ricf_complete_params PG s.vs_params) G tn s t /\
  ricf_live_stack_agree D ids tn maps stk targets s t /\
  cf.cf_state = s /\ cf.cf_params = PG /\ cf.cf_prov = G /\
  cf.cf_tvar = tn.t_var /\
  ricf_params_agree sites newPG args args' /\ ricf_sites_ok sites /\
  ircf_cross tn (ricf_site_triples sites) s t /\
  (if NULL args then 0w else LAST args) =
    (if NULL args' then 0w else LAST args') /\
  setup_callee fn args s = SOME cs /\
  setup_callee fn args' t = SOME ct ==>
  ricf_live_boundary_core D ids (cf::stk) newPG FEMPTY
    (tn with t_var := FEMPTY) fn sites (oldsites::maps) (t::targets)
    FEMPTY (tn with t_var := FEMPTY) cs ct
Proof
  strip_tac >>
  `ricf_frame_agree D (ircf_dead ids s stk) sites newPG FEMPTY
     (tn with t_var := FEMPTY) cs ct`
    by (irule ricf_setup_callee_frame >> metis_tac[]) >>
  `LENGTH newPG = LENGTH cs.vs_params`
    by metis_tac[ricf_setup_callee_params, ricf_params_agree_def] >>
  `ricf_complete_params newPG cs.vs_params = newPG`
    by simp[ricf_complete_params_def] >>
  simp[ricf_live_boundary_core_def] >> conj_tac
  >- (fs[setup_callee_def] >> gvs[AllCaseEqs()]) >>
  conj_tac
  >- (fs[setup_callee_def] >> gvs[AllCaseEqs()]) >>
  conj_tac
  >- (drule_all ricf_live_callee_dead >> simp[] >> metis_tac[]) >>
  metis_tac[ricf_live_nested_push]
QED

(* Concrete non-vacuity instance: a historical zero differs from one,
   while an equal live write of two clears the only tainted address.
   The saved target memory is never rewritten to make the probe pass. *)
Theorem ricf_live_equal_write_probe:
  let a = s0 with vs_memory := [];
      cf = frame with <| cf_state := a; cf_params := [] |>;
      u = write_memory_with_expansion 0 [2w] a in
  read_byte 0 cf.cf_state.vs_memory <>
    read_byte 0 (a with vs_memory := [1w]).vs_memory /\
  read_byte 0 u.vs_memory = 2w /\
  ricf_live_stack_agree D ids (tn with t_mem := {0})
    [FEMPTY] [cf] [a with vs_memory := [1w]] u u /\
  ricf_live_stack_agree D ids (tn with t_mem := {})
    [FEMPTY] [cf] [a with vs_memory := [1w]] u u
Proof
  simp_tac bool_ss [LET_THM] >>
  `read_byte 0 ([]:byte list) <> read_byte 0 [1w]`
    by simp[read_byte_def] >>
  simp[write_memory_with_expansion_def, read_byte_def] >>
  simp[ricf_live_stack_cons, ricf_live_frame_decompose,
    ricf_live_local_agree_def, merge_callee_state_def,
    ricf_value_agree_empty, word_agree_except_def,
    ricf_params_agree_empty, ricf_complete_params_length,
    ricf_sites_ok_def, ricf_site_triples_def, ircf_cross_def,
    ld_shared_agree_refl]
QED

(* Suspended maps are immutable indices of a function run.  Only the
   current frame's map and the saved target witnesses are existential. *)
Definition ricf_indexed_boundary_def:
  ricf_indexed_boundary D ids maps stk PG G tn fn s t <=>
    ?sites targets G0 tn0.
      ricf_live_boundary_core D ids stk PG G tn fn
        sites maps targets G0 tn0 s t
End

Definition ricf_indexed_return_def:
  ricf_indexed_return D ids maps stk (PG:(num # num) option list)
      (G:(string,num # num) fmap) tn (fn:ir_function) (ret:internal_return) s t <=>
    ?targets. ricf_live_return_core D ids stk maps targets tn s t
End

Theorem ricf_indexed_initial:
  s.vs_prev_bb = NONE /\ taint_agree D (ircf_dead ids s []) tn s s ==>
  ricf_indexed_boundary D ids [] [] [] FEMPTY tn fn s s
Proof
  strip_tac >>
  simp[ricf_indexed_boundary_def, ricf_live_boundary_core_def] >>
  qexistsl [`FEMPTY`, `[]`] >>
  simp[ricf_frame_agree_completed_identity]
QED

Theorem ricf_indexed_saved_locals:
  ricf_live_boundary_core D ids stk PG G tn fn sites maps targets G0 tn0 s t ==>
  LENGTH targets = LENGTH stk /\
  (!j. j < LENGTH stk ==>
    ricf_live_local_agree (EL j maps)
      (ricf_complete_params (EL j stk).cf_params (EL j stk).cf_state.vs_params)
      (EL j stk).cf_prov (EL j stk).cf_tvar
      (EL j stk).cf_state (EL j targets))
Proof
  simp[ricf_live_boundary_core_def, ricf_live_stack_agree_def,
       ricf_live_frame_decompose] >> metis_tac[]
QED

Theorem ricf_indexed_return_elim:
  ricf_indexed_return D ids maps stk PG G tn fn ret s t /\
  LENGTH actual = LENGTH stk /\
  (!j. j < LENGTH stk ==>
    ricf_live_local_agree (EL j maps)
      (ricf_complete_params (EL j stk).cf_params (EL j stk).cf_state.vs_params)
      (EL j stk).cf_prov (EL j stk).cf_tvar
      (EL j stk).cf_state (EL j actual)) ==>
  ricf_live_return_core D ids stk maps actual tn s t
Proof
  simp[ricf_indexed_return_def] >> metis_tac[ricf_live_return_reanchor]
QED

Theorem ricf_indexed_return_caller:
  ricf_indexed_return D ids (sites::maps) (cf::stk) PG G tn fn ret s t /\
  LENGTH (caller::actual) = LENGTH (cf::stk) /\
  (!j. j < LENGTH (cf::stk) ==>
    ricf_live_local_agree (EL j (sites::maps))
      (ricf_complete_params (EL j (cf::stk)).cf_params
        (EL j (cf::stk)).cf_state.vs_params)
      (EL j (cf::stk)).cf_prov (EL j (cf::stk)).cf_tvar
      (EL j (cf::stk)).cf_state (EL j (caller::actual))) ==>
  ricf_frame_agree D (ircf_dead ids cf.cf_state stk) sites
    (ricf_complete_params cf.cf_params cf.cf_state.vs_params)
    cf.cf_prov (tn with t_var := cf.cf_tvar)
    (merge_callee_state cf.cf_state s) (merge_callee_state caller t)
Proof
  strip_tac >> irule ricf_live_return_actual_caller >>
  metis_tac[ricf_indexed_return_elim]
QED

Theorem ricf_indexed_nested_entry:
  ricf_frame_agree D (ircf_dead ids s stk) oldsites
    (ricf_complete_params PG s.vs_params) G tn s t /\
  ricf_live_stack_agree D ids tn maps stk targets s t /\
  cf.cf_state = s /\ cf.cf_params = PG /\ cf.cf_prov = G /\
  cf.cf_tvar = tn.t_var /\
  ricf_params_agree sites newPG args args' /\ ricf_sites_ok sites /\
  ircf_cross tn (ricf_site_triples sites) s t /\
  (if NULL args then 0w else LAST args) =
    (if NULL args' then 0w else LAST args') /\
  setup_callee fn args s = SOME cs /\
  setup_callee fn args' t = SOME ct ==>
  ricf_indexed_boundary D ids (oldsites::maps) (cf::stk) newPG FEMPTY
    (tn with t_var := FEMPTY) fn cs ct
Proof
  strip_tac >> simp[ricf_indexed_boundary_def] >>
  drule_all ricf_live_nested_entry >> metis_tac[]
QED

(* The universal quantifier over maps is OUTSIDE fn_sim_below: each
   recursive call specializes it to its own oldsites::maps. *)
Definition ricf_indexed_sim_below_def:
  ricf_indexed_sim_below D ids vs C C' n <=>
    !maps. fn_sim_below D vs C C'
      (ricf_indexed_boundary D ids maps) (ricf_indexed_return D ids maps) n
End

Theorem ricf_indexed_sim_below_elim:
  ricf_indexed_sim_below D ids vs C C' n /\ k < n /\
  MEM fn C.ctx_functions /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  ricf_indexed_boundary D ids maps stk PG G tn fn s t /\
  block_reach vs C stk PG G tn fn s /\
  terminates (run_blocks k C fn s) ==>
  ?m. fn_run_rel D (ricf_indexed_return D ids maps) stk PG fn
    (run_blocks k C fn s) (run_blocks m C' fn' t)
Proof
  simp[ricf_indexed_sim_below_def, fn_sim_below_def] >> metis_tac[]
QED

Definition ricf_indexed_block_step_rel_def:
  ricf_indexed_block_step_rel D ids maps vs C stk PG fn r r' <=>
    block_step_rel D vs C (ricf_indexed_boundary D ids maps)
      (ricf_indexed_return D ids maps) stk PG fn r r'
End

(* Save the actual target list before recursion.  Returned targets are
   deliberately unconstrained: only the suspended-map INDEX is shared. *)
Theorem ricf_indexed_call_return:
  ricf_live_boundary_core D ids stk PG G tn fn sites maps actual G0 tn0 s t /\
  ricf_indexed_return D ids maps stk PG' G' un fn' ret u v ==>
  ricf_live_return_core D ids stk maps actual un u v
Proof
  strip_tac >> drule ricf_indexed_saved_locals >> strip_tac >>
  metis_tac[ricf_indexed_return_elim]
QED

(* Two nonempty maps with genuinely displaced pointer parameters.  The
   inherited frame has a DIFFERENT translation, so a tail cannot be lost
   or replaced with the current frame map.  Live shared memory is empty;
   saved locals are nontrivial and do not observe historical memory. *)
Theorem ricf_indexed_displaced_stack_probe:
  let headmap = FEMPTY |+ ((4,1),(4,8,1));
      tailmap = FEMPTY |+ ((12,1),(12,16,1));
      a = s0 with <| vs_vars := FEMPTY; vs_params := [4w]; vs_alloca_next := 0 |>;
      b = s0 with <| vs_vars := FEMPTY; vs_params := [12w]; vs_alloca_next := 0 |>;
      cf = frame with <| cf_state := a; cf_params := [SOME (4,1)];
                         cf_prov := FEMPTY; cf_tvar := FEMPTY |>;
      older = frame with <| cf_state := b; cf_params := [SOME (12,1)];
                            cf_prov := FEMPTY; cf_tvar := FEMPTY |>;
      actual = [a with vs_params := [8w]; b with vs_params := [16w]];
      live = s0 with vs_memory := [] in
  4 <> 8 /\ 12 <> 16 /\
  ricf_live_stack_agree D ids (tn with t_mem := {})
    [headmap;tailmap] [cf;older] actual live live
Proof
  simp_tac bool_ss [LET_THM] >>
  simp[ricf_live_stack_cons, ricf_live_frame_decompose,
       ricf_live_local_agree_def, merge_callee_state_def,
       ricf_complete_params_def, ricf_params_agree_def,
       ricf_sites_ok_def, ricf_value_agree_def, ld_value_agree_def,
       ricf_site_triples_def, ircf_cross_def, read_byte_def,
       ld_shared_agree_refl, FLOOKUP_UPDATE, venom_state_component_equality,
       wordsTheory.WORD_ADD_SUB2]
QED

Theorem ricf_indexed_entry_return_probe:
  let headmap = FEMPTY |+ ((4,1),(4,8,1));
      tailmap = FEMPTY |+ ((12,1),(12,16,1));
      a = s0 with <| vs_vars := FEMPTY; vs_params := [4w]; vs_alloca_next := 0 |>;
      b = s0 with <| vs_vars := FEMPTY; vs_params := [12w]; vs_alloca_next := 0 |>;
      cf = frame with <| cf_state := a; cf_params := [SOME (4,1)];
                         cf_prov := FEMPTY; cf_tvar := FEMPTY |>;
      older = frame with <| cf_state := b; cf_params := [SOME (12,1)];
                            cf_prov := FEMPTY; cf_tvar := FEMPTY |>;
      actual = [a with vs_params := [8w]; b with vs_params := [16w]];
      live = s0 with <| vs_memory := []; vs_vars := FEMPTY;
                       vs_params := []; vs_prev_bb := NONE |>;
      clean = tn with t_mem := {} in
  4 <> 8 /\ 12 <> 16 /\
  ricf_live_boundary_core D ids [cf;older] [] FEMPTY clean fn
    FEMPTY [headmap;tailmap] actual FEMPTY clean live live /\
  ricf_indexed_boundary D ids [headmap;tailmap] [cf;older]
    [] FEMPTY clean fn live live /\
  (!PG G un fn' ret u v.
    ricf_indexed_return D ids [headmap;tailmap] [cf;older] PG G un fn' ret u v ==>
    ricf_live_return_core D ids [cf;older] [headmap;tailmap] actual un u v)
Proof
  simp_tac bool_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `ricf_live_boundary_core D ids stk [] FEMPTY clean fn
    FEMPTY maps actual FEMPTY clean live live` >>
  `ricf_live_stack_agree D ids clean maps stk actual live live`
    by (simp[Abbr `stk`, Abbr `clean`, Abbr `maps`, Abbr `actual`, Abbr `live`,
        ricf_live_stack_cons, ricf_live_frame_decompose,
        ricf_live_local_agree_def, merge_callee_state_def,
        ricf_complete_params_def, ricf_params_agree_def,
        ricf_sites_ok_def, ricf_value_agree_def, ld_value_agree_def,
        ricf_site_triples_def, ircf_cross_def, read_byte_def,
        ld_shared_agree_refl, FLOOKUP_UPDATE, venom_state_component_equality,
        wordsTheory.WORD_ADD_SUB2]) >>
  `ricf_live_boundary_core D ids stk [] FEMPTY clean fn
     FEMPTY maps actual FEMPTY clean live live`
    by (simp[ricf_live_boundary_core_def, Abbr `live`,
             ricf_frame_agree_completed_identity, taint_agree_def,
             ld_shared_agree_refl, word_agree_except_def,
             venom_state_component_equality] >>
        irule ricf_frame_agree_completed_identity >>
        simp[taint_agree_def, ld_shared_agree_refl,
             word_agree_except_def, venom_state_component_equality]) >>
  simp[] >> conj_tac
  >- (simp[ricf_indexed_boundary_def] >> metis_tac[]) >>
  metis_tac[ricf_indexed_call_return]
QED

(* Copy certificates are independent of the maps that translate locals.
   Both suspended indices are fixed throughout a recursive function run. *)
Definition ricf_cert_crosses_def:
  ricf_cert_crosses tn curs stk s t <=>
    LENGTH curs = LENGTH stk /\ EVERY (\gam. ircf_cross tn gam s t) curs
End

Definition ricf_cert_core_def:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t <=>
    ricf_live_boundary_core D ids stk PG G tn fn
      sites maps targets G0 tn0 s t /\
    ircf_cross tn0 cur s t /\ ricf_cert_crosses tn0 curs stk s t
End

Definition ricf_cert_boundary_def:
  ricf_cert_boundary D ids maps curs stk PG G tn fn s t <=>
    ?sites targets G0 tn0 cur.
      ricf_cert_core D ids stk PG G tn fn
        sites maps targets G0 tn0 cur curs s t
End

Definition ricf_cert_return_core_def:
  ricf_cert_return_core D ids stk maps targets curs tn s t <=>
    ricf_live_return_core D ids stk maps targets tn s t /\
    ricf_cert_crosses tn curs stk s t
End

Definition ricf_cert_return_def:
  ricf_cert_return D ids maps curs stk (PG:(num # num) option list)
      (G:(string,num # num) fmap) tn (fn:ir_function) (ret:internal_return) s t <=>
    ?targets. ricf_cert_return_core D ids stk maps targets curs tn s t
End

Definition ricf_cert_sim_below_def:
  ricf_cert_sim_below D ids vs C C' n <=>
    !maps curs. fn_sim_below D vs C C'
      (ricf_cert_boundary D ids maps curs) (ricf_cert_return D ids maps curs) n
End

Theorem ricf_cert_crosses_cons:
  ricf_cert_crosses tn (cur::curs) (cf::stk) s t <=>
  ircf_cross tn cur s t /\ ricf_cert_crosses tn curs stk s t
Proof
  simp[ricf_cert_crosses_def] >> metis_tac[]
QED

Theorem ricf_cert_core_live:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t ==>
  ricf_live_boundary_core D ids stk PG G tn fn
    sites maps targets G0 tn0 s t
Proof
  simp[ricf_cert_core_def]
QED

Theorem ricf_cert_core_current_cross:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t ==>
  ircf_cross tn0 cur s t
Proof
  simp[ricf_cert_core_def]
QED

Theorem ricf_cert_core_suspended_cross:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t ==>
  ricf_cert_crosses tn0 curs stk s t
Proof
  simp[ricf_cert_core_def]
QED

Theorem ricf_cert_boundary_live:
  ricf_cert_boundary D ids maps curs stk PG G tn fn s t ==>
  ricf_indexed_boundary D ids maps stk PG G tn fn s t
Proof
  simp[ricf_cert_boundary_def, ricf_cert_core_def, ricf_indexed_boundary_def] >>
  metis_tac[]
QED

Theorem ricf_cert_core_intro:
  ricf_live_boundary_core D ids stk PG G tn fn sites maps targets G0 tn0 s t /\
  ircf_cross tn0 cur s t /\ ricf_cert_crosses tn0 curs stk s t ==>
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t
Proof
  simp[ricf_cert_core_def]
QED

Theorem ricf_cert_initial:
  s.vs_prev_bb = NONE /\ taint_agree D (ircf_dead ids s []) tn s s ==>
  ricf_cert_boundary D ids [] [] [] [] FEMPTY tn fn s s
Proof
  strip_tac >>
  simp[ricf_cert_boundary_def, ricf_cert_core_def, ricf_cert_crosses_def,
       ricf_live_boundary_core_def] >>
  qexistsl [`FEMPTY`, `[]`, `{}`] >>
  simp[ricf_frame_agree_completed_identity, ricf_live_stack_agree_def,
       ircf_cross_def]
QED

Theorem ricf_cert_saved_locals:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t ==>
  LENGTH targets = LENGTH stk /\
  (!j. j < LENGTH stk ==>
    ricf_live_local_agree (EL j maps)
      (ricf_complete_params (EL j stk).cf_params (EL j stk).cf_state.vs_params)
      (EL j stk).cf_prov (EL j stk).cf_tvar
      (EL j stk).cf_state (EL j targets))
Proof
  metis_tac[ricf_cert_core_live, ricf_indexed_saved_locals]
QED

Theorem ricf_cert_return_reanchor:
  ricf_cert_return_core D ids stk maps targets curs tn s t /\
  LENGTH actual = LENGTH stk /\
  (!j. j < LENGTH stk ==>
    ricf_live_local_agree (EL j maps)
      (ricf_complete_params (EL j stk).cf_params (EL j stk).cf_state.vs_params)
      (EL j stk).cf_prov (EL j stk).cf_tvar
      (EL j stk).cf_state (EL j actual)) ==>
  ricf_cert_return_core D ids stk maps actual curs tn s t
Proof
  simp[ricf_cert_return_core_def] >> metis_tac[ricf_live_return_reanchor]
QED

Theorem ricf_cert_call_return:
  ricf_cert_core D ids stk PG G tn fn sites maps actual G0 tn0 cur curs s t /\
  ricf_cert_return D ids maps curs stk PG' G' un fn' ret u v ==>
  ricf_cert_return_core D ids stk maps actual curs un u v
Proof
  simp[ricf_cert_return_def] >> rpt strip_tac >>
  drule ricf_cert_saved_locals >> strip_tac >>
  metis_tac[ricf_cert_return_reanchor]
QED

(* Byte/taint framing is demanded on LIVE states for every suspended
   certificate; historical caller memory is deliberately absent. *)
Theorem ricf_cert_crosses_refresh:
  ricf_cert_crosses tn curs stk s t /\
  (!gam db sb sz k. MEM gam curs /\ (db,sb,sz) IN gam /\ k < sz ==>
    (db+k IN un.t_mem <=> db+k IN tn.t_mem) /\
    (sb+k IN un.t_mem <=> sb+k IN tn.t_mem) /\
    read_byte (db+k) u.vs_memory = read_byte (db+k) s.vs_memory /\
    read_byte (sb+k) v.vs_memory = read_byte (sb+k) t.vs_memory) ==>
  ricf_cert_crosses un curs stk u v
Proof
  simp[ricf_cert_crosses_def, EVERY_MEM, ircf_cross_def] >> metis_tac[]
QED

Theorem ricf_cert_sim_below_elim:
  ricf_cert_sim_below D ids vs C C' n /\ k < n /\
  MEM fn C.ctx_functions /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  ricf_cert_boundary D ids maps curs stk PG G tn fn s t /\
  block_reach vs C stk PG G tn fn s /\
  terminates (run_blocks k C fn s) ==>
  ?m. fn_run_rel D (ricf_cert_return D ids maps curs) stk PG fn
    (run_blocks k C fn s) (run_blocks m C' fn' t)
Proof
  simp[ricf_cert_sim_below_def, fn_sim_below_def] >> metis_tac[]
QED
