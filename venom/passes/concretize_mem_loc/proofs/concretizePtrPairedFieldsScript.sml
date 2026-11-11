Theory concretizePtrPairedFields
Ancestors
  concretizePtrStructuralTranscript concretizePtrValueSelection
  concretizePtrPrefixLedger concretizePtrStagePlacements concretizePtrBytes
  concretizeStepStructure concretizeStepShape
  concretizeStepRetpc concretizeStageShape concretizeStepContract
  concretizePtrOpaqueRetpc
  list rich_list arithmetic pair pred_set

(* The global map is for relocation only; production rewrites have their
   own per-function maps. Metadata is deliberately not equated. *)
Definition ptr_paired_code_def:
  ptr_paired_code R local_positions positions f g <=>
    R f g /\ fn_entry_label f = fn_entry_label g /\
    g.fn_blocks = (concretize_function_with_positions (local_positions f) f).fn_blocks /\
    (!bb inst. MEM bb f.fn_blocks /\ MEM inst bb.bb_instructions /\
      inst.inst_opcode = ALLOCA ==>
      FLOOKUP (local_positions f) (Allocation inst.inst_id) =
        OPTION_MAP FST (FLOOKUP positions (Allocation inst.inst_id)))
End

Definition ptr_paired_cursor_def:
  ptr_paired_cursor local_positions a at <=>
    a.po_state.vs_current_bb = at.po_state.vs_current_bb /\
    a.po_state.vs_prev_bb = at.po_state.vs_prev_bb /\
    ?bb bbt indices.
      lookup_block a.po_state.vs_current_bb a.po_fn.fn_blocks = SOME bb /\
      lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bbt /\
      MEM bb a.po_fn.fn_blocks /\ MEM bbt at.po_fn.fn_blocks /\
      ptr_ledger_block_alignment (local_positions a.po_fn)
        bb.bb_instructions bbt.bb_instructions indices /\
      at.po_state.vs_inst_idx < LENGTH indices /\
      a.po_state.vs_inst_idx <= EL at.po_state.vs_inst_idx indices /\
      (!k. a.po_state.vs_inst_idx <= k /\
        k < EL at.po_state.vs_inst_idx indices ==>
        (EL k bb.bb_instructions).inst_opcode = NOP) /\
      a.po_inst = EL a.po_state.vs_inst_idx bb.bb_instructions /\
      at.po_inst = EL at.po_state.vs_inst_idx bbt.bb_instructions
End

Definition ptr_paired_params_def:
  ptr_paired_params positions a at
      (tokens,registry,births,PT,TG,saved,entries) <=>
    (PT = [] /\ a.po_state.vs_params = at.po_state.vs_params) \/
    ptr_args_transport births positions PT
      (REPLICATE (LENGTH a.po_state.vs_params) {})
      a.po_state.vs_params at.po_state.vs_params
End

Definition ptr_paired_frame_def:
  ptr_paired_frame frame obs <=>
    frame.cf_fn = obs.po_fn /\ frame.cf_inst = obs.po_inst /\
    frame.cf_state = obs.po_state /\ frame.cf_params = obs.po_params /\
    frame.cf_prov = obs.po_prov /\ frame.cf_tvar = obs.po_taint.t_var
End

Definition ptr_paired_saved_tags_def:
  ptr_paired_saved_tags tags (tokens,registry,births,PT,TG,saved,entries) <=>
    tags = (PT,TG)
End

Definition ptr_paired_call_def:
  ptr_paired_call h ht done H frame framet tags (n,j) <=>
    j < LENGTH done /\ n = EL j done /\
    ptr_paired_frame frame (EL n h) /\
    ptr_paired_frame framet (EL j ht) /\
    (EL n h).po_inst.inst_opcode = INVOKE /\
    (EL j ht).po_inst.inst_opcode = INVOKE /\
    ptr_paired_saved_tags tags (EL n H)
End

Definition ptr_paired_callers_def:
  ptr_paired_callers h ht done H a at saved calls <=>
    LENGTH calls = LENGTH a.po_stack /\
    LENGTH calls = LENGTH at.po_stack /\ LENGTH calls = LENGTH saved /\
    (!k. k < LENGTH calls ==>
      ptr_paired_call h ht done H (EL k a.po_stack) (EL k at.po_stack)
        (EL k saved) (EL k calls))
End

Definition ptr_paired_write_owner_def:
  ptr_paired_write_owner (lo:num) positions (rho:num -> num) xs
      (tokens,registry,births,PT,TG,saved,entries) <=>
    !x. x IN xs ==>
      (x < lo /\ rho x = x) \/
      (?token aid base sz pos k. MEM token tokens /\ k < sz /\ x = base + k /\ rho x = pos + k /\
        FLOOKUP births (token,aid) = SOME (base,sz) /\
        FLOOKUP positions (Allocation aid) = SOME (pos,sz))
End

Definition ptr_paired_write_def:
  ptr_paired_write lo positions C Ct h ht done H (n,j,rho) <=>
    j < LENGTH done /\ n = EL j done /\ SUC n < LENGTH h /\
    SUC j < LENGTH ht /\
    range_bytes (step_writes (EL n h).po_inst (EL n h).po_state
      (EL (SUC n) h).po_state) <> {} /\
    ptr_ledger_write_pair C Ct rho (EL n h) (EL (SUC n) h)
      (EL j ht) (EL (SUC j) ht) /\
    ptr_paired_write_owner lo positions rho
      (range_bytes (step_writes (EL n h).po_inst (EL n h).po_state
        (EL (SUC n) h).po_state)) (EL (SUC n) H)
End

Definition ptr_paired_writes_def:
  ptr_paired_writes lo positions C Ct h ht done H W <=>
    EVERY (ptr_paired_write lo positions C Ct h ht done H) W /\
    ALL_DISTINCT (MAP (\(n,j,rho). j) W) /\
    (!j. j < LENGTH done /\
      ~is_terminator (EL (EL j done) h).po_inst.inst_opcode /\
      (EL (EL j done) h).po_inst.inst_opcode <> INVOKE /\
      range_bytes (step_writes (EL (EL j done) h).po_inst
        (EL (EL j done) h).po_state (EL (SUC (EL j done)) h).po_state) <> {} ==>
      ?rho. MEM (EL j done,j,rho) W)
End

(* This is an origin, not agreement of any later endpoint memories. *)
Definition ptr_paired_initial_origin_def:
  ptr_paired_initial_origin lo (vs0:venom_state) x y value <=>
    x < lo /\ y = x /\ value = read_byte x vs0.vs_memory
End

Theorem ptr_paired_initial_sentinel:
  ptr_bytes_agree {x | x < lo} I vs0.vs_memory vs0.vs_memory
Proof
  simp[ptr_bytes_agree_def]
QED

Theorem ptr_paired_write_owner_byte:
  !lo positions (rho:num -> num) xs tokens registry births PT TG saved entries x.
  ptr_paired_write_owner lo positions rho xs
    (tokens,registry,births,PT,TG,saved,entries) /\ x IN xs ==>
  (x < lo /\ rho x = x) \/
  (?token aid base sz pos k. MEM token tokens /\ k < sz /\ x = base + k /\ rho x = pos + k /\
    FLOOKUP births (token,aid) = SOME (base,sz) /\
    FLOOKUP positions (Allocation aid) = SOME (pos,sz))
Proof
  simp[ptr_paired_write_owner_def]
QED

(* Only prefix geometry is used here; there is no operational extension
   or current-memory agreement premise. *)
Theorem ptr_paired_write_retained:
  !rho. LENGTH H = LENGTH h /\
  ptr_paired_write lo positions C Ct h ht done H (n,j,rho) ==>
  ptr_paired_write lo positions C Ct (h ++ hs) (ht ++ ts)
    (done ++ ds) (H ++ snapshots) (n,j,rho)
Proof
  rpt gen_tac >> simp[ptr_paired_write_def] >> strip_tac >>
  `n < LENGTH h /\ j < LENGTH ht /\ SUC n < LENGTH H` by decide_tac >>
  gvs[EL_APPEND_EQN]
QED

Theorem ptr_paired_call_retained:
  n < LENGTH h /\ j < LENGTH ht /\ LENGTH H = LENGTH h /\
  ptr_paired_call h ht done H frame framet tags (n,j) ==>
  ptr_paired_call (h ++ hs) (ht ++ ts) (done ++ ds) (H ++ snapshots)
    frame framet tags (n,j)
Proof
  simp[ptr_paired_call_def] >> strip_tac >> gvs[EL_APPEND_EQN]
QED

Theorem ptr_paired_write_event:
  !W rho. ptr_paired_writes lo positions C Ct h ht done H W /\
  MEM (n,j,rho) W ==>
  ptr_paired_write lo positions C Ct h ht done H (n,j,rho)
Proof
  simp[ptr_paired_writes_def, EVERY_MEM]
QED

Theorem ptr_paired_writes_retained:
  !W. ptr_paired_writes lo positions C Ct h ht done H W /\
  LENGTH H = LENGTH h ==>
  EVERY (ptr_paired_write lo positions C Ct (h ++ hs) (ht ++ ts)
    (done ++ ds) (H ++ snapshots)) W
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  PairCases_on `e` >> irule ptr_paired_write_retained >>
  goal_assum (drule_at Any) >>
  irule ptr_paired_write_event >> goal_assum (drule_at Any) >> simp[]
QED

Theorem ptr_paired_callers_retained:
  ptr_paired_callers h ht done H a at saved calls /\
  EVERY (\n. n < LENGTH h) done /\ LENGTH done < LENGTH ht /\
  LENGTH H = LENGTH h /\ b.po_stack = a.po_stack /\ bt.po_stack = at.po_stack ==>
  ptr_paired_callers (h ++ hs) (ht ++ ts) (done ++ ds) (H ++ snapshots)
    b bt saved calls
Proof
  rewrite_tac[ptr_paired_callers_def] >> strip_tac >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!k. _` (qspec_then `k` mp_tac) >> simp[] >>
  Cases_on `EL k calls` >> strip_tac >>
  irule ptr_paired_call_retained >>
  goal_assum (drule_at Any) >> gvs[ptr_paired_call_def, EVERY_EL]
QED

Theorem ptr_paired_writes_gap:
  !ws. ptr_paired_writes lo positions C Ct h ht done H ws /\
  LENGTH H = LENGTH h /\ EVERY (\n. SUC n < LENGTH h) done ==>
  ptr_paired_writes lo positions C Ct (h ++ hs) ht done (H ++ snapshots) ws
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (ptr_paired_write lo positions C Ct (h ++ hs) ht done
    (H ++ snapshots)) ws` by
    (drule_all ptr_paired_writes_retained >>
     disch_then (qspecl_then [`[]`,`snapshots`,`hs`,`[]`] mp_tac) >> simp[]) >>
  rewrite_tac[ptr_paired_writes_def] >> conj_tac >- simp[] >>
  conj_tac >- gvs[ptr_paired_writes_def] >>
  rpt strip_tac >>
  `SUC (EL j done) < LENGTH h` by gvs[EVERY_EL] >>
  `EL j done < LENGTH h` by decide_tac >>
  gvs[EL_APPEND_EQN, ptr_paired_writes_def] >>
  first_x_assum irule >> simp[]
QED

(* The optional new ledger entry is local to the departing endpoint. *)
Theorem ptr_paired_writes_pair:
  !ws extra. ptr_paired_writes lo positions C Ct h ht done H ws /\
  LENGTH H = LENGTH h /\ 0 < LENGTH h /\
  LENGTH ht = SUC (LENGTH done) /\ EVERY (\n. SUC n < LENGTH h) done /\
  (extra = [] \/ ?rho. extra = [(LENGTH h - 1,LENGTH done,rho)]) /\
  EVERY (ptr_paired_write lo positions C Ct (h ++ [b]) (ht ++ [bt])
    (done ++ [LENGTH h - 1]) (H ++ [snapshot])) extra /\
  (~is_terminator (LAST h).po_inst.inst_opcode /\
    (LAST h).po_inst.inst_opcode <> INVOKE /\
    range_bytes (step_writes (LAST h).po_inst (LAST h).po_state b.po_state) <> {} ==>
    ?rho. MEM (LENGTH h - 1,LENGTH done,rho) extra) ==>
  ptr_paired_writes lo positions C Ct (h ++ [b]) (ht ++ [bt])
    (done ++ [LENGTH h - 1]) (H ++ [snapshot]) (ws ++ extra)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY (ptr_paired_write lo positions C Ct (h ++ [b]) (ht ++ [bt])
    (done ++ [LENGTH h - 1]) (H ++ [snapshot])) ws` by
    (drule_all ptr_paired_writes_retained >> simp[]) >>
  rewrite_tac[ptr_paired_writes_def] >> conj_tac >- simp[EVERY_APPEND] >>
  conj_tac
  >- (qpat_x_assum `_ ==> ?rho. MEM _ extra` kall_tac >>
      qpat_x_assum `extra = [] \/ _` strip_assume_tac >> gvs[]
      >- gvs[ptr_paired_writes_def] >>
      simp[ALL_DISTINCT_APPEND] >> conj_tac
      >- gvs[ptr_paired_writes_def] >>
      simp[MEM_MAP, FORALL_PROD] >> rpt strip_tac >>
      drule_all ptr_paired_write_event >>
      simp[ptr_paired_write_def]) >>
  rpt strip_tac >> Cases_on `j < LENGTH done`
  >- (`SUC (EL j done) < LENGTH h` by gvs[EVERY_EL] >>
      `EL j done < LENGTH h` by decide_tac >>
      gvs[EL_APPEND_EQN, ptr_paired_writes_def] >>
      first_x_assum drule >> simp[] >> metis_tac[]) >>
  `j = LENGTH done` by gvs[] >>
  `LAST h = EL (LENGTH h - 1) h` by
    (`h <> []` by (Cases_on `h` >> fs[]) >>
     `PRE (LENGTH h) = LENGTH h - 1` by decide_tac >> simp[LAST_EL]) >>
  `SUC (LENGTH h - 1) = LENGTH h` by decide_tac >>
  gvs[EL_APPEND_EQN] >> metis_tac[]
QED

Theorem ptr_paired_write_owned_byte:
  !ws rho. ptr_paired_writes lo positions C Ct h ht done H ws /\
  MEM (n,j,rho) ws /\
  EL (SUC n) H = (tokens,registry,births,PT,TG,saved,entries) /\
  x IN range_bytes (step_writes (EL n h).po_inst (EL n h).po_state
    (EL (SUC n) h).po_state) ==>
  (x < lo /\ rho x = x) \/
  (?token aid base sz pos k. MEM token tokens /\ k < sz /\ x = base + k /\ rho x = pos + k /\
    FLOOKUP births (token,aid) = SOME (base,sz) /\
    FLOOKUP positions (Allocation aid) = SOME (pos,sz))
Proof
  rpt gen_tac >> strip_tac >> drule_all ptr_paired_write_event >>
  simp[ptr_paired_write_def] >> strip_tac >>
  drule_all ptr_paired_write_owner_byte >> simp[]
QED

Theorem ptr_paired_code_retpc:
  ptr_paired_code R lp positions f g ==>
  (retpc_var f x <=> retpc_var g x)
Proof
  simp[ptr_paired_code_def, unitShapeDefsTheory.retpc_var_def] >> strip_tac >>
  drule concretize_blocks_copy_phi >>
  disch_then (qspecl_then [`x`,`RETPC_PARAM`] mp_tac) >>
  simp[concretize_positions_copy_phi]
QED

(* The historical mixed fact is an input here. C1.10.8 installs it in the
   sample certificate; restoration never reinterprets caller variables
   using a callee token. *)
Theorem ptr_paired_call_mixed:
  ptr_paired_call h ht done H frame framet tags (n,j) /\
  ptr_mixed_vars births positions TG (EL n h).po_taint
    (EL n h).po_fn (EL j ht).po_fn (EL n h).po_state (EL j ht).po_state ==>
  ptr_mixed_vars births positions TG (EL n h).po_taint
    frame.cf_fn framet.cf_fn frame.cf_state framet.cf_state
Proof
  simp[ptr_paired_call_def, ptr_paired_frame_def] >> metis_tac[]
QED

Theorem ptr_paired_callers_mixed:
  ptr_paired_callers h ht done H a at saved calls /\ k < LENGTH calls /\
  EL k calls = (n,j) /\
  ptr_mixed_vars births positions TG (EL n h).po_taint
    (EL n h).po_fn (EL j ht).po_fn (EL n h).po_state (EL j ht).po_state ==>
  ptr_mixed_vars births positions TG (EL n h).po_taint
    (EL k a.po_stack).cf_fn (EL k at.po_stack).cf_fn
    (EL k a.po_stack).cf_state (EL k at.po_stack).cf_state
Proof
  strip_tac >> fs[ptr_paired_callers_def] >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[] >> strip_tac >>
  drule_all ptr_paired_call_mixed >> simp[]
QED
