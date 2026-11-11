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
