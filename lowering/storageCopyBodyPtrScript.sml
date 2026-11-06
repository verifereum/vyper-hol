(* Counted fixed-instruction boundaries for the storage-copy body.
   Arbitrary payload taint is retained at the actual checked endpoint. *)
Theory storageCopyBodyPtr
Ancestors
  storageCopyControlPtr typedCopyLoopHeaderPtr payloadLoadStorePtr
  exprLoweringProps exprSimStorageCopy decoderGhostFramePtr fragExec
  stmtAppendStorageRunPtr fragGasSeqPtr fragGasPathPtr ptrSafeRun ptrDiscipline
  venomExecSemantics venomExecProofs venomInst venomState bodyPtrDefs
  codegenRel contextCodegenRel finite_map pred_set words list arithmetic

Theorem storage_copy_load_step:
  eval_operand a s = SOME slot ==>
  step_inst_base (mk_inst id (if tr then TLOAD else SLOAD) [a] [out]) s =
    OK (update_var out (if tr then tload slot s else sload slot s) s)
Proof
  strip_tac >> Cases_on `tr` >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_read1_def]
QED

Theorem storage_copy_load_path_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id (if tr then TLOAD else SLOAD) [a] [out]) /\
  eval_operand a s = SOME slot /\ op_taint tn a = {} /\
  ~ctx_has_dalloca ctx ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+
      (out,key_taint (if tr then tn.t_trans else tn.t_stor) slot))
    (OK (update_var out (if tr then tload slot s else sload slot s) s
      with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  drule storage_copy_load_step >>
  disch_then (qspecl_then [`tr`, `out`, `id`] assume_tac) >>
  `ptr_inst_ok D 0 0 ctx fn G tn
    (mk_inst id (if tr then TLOAD else SLOAD) [a] [out]) s` by
    (irule ptr_inst_ok_storage_load_payload >>
     simp[update_var_def] >> metis_tac[]) >>
  `~is_terminator
      (mk_inst id (if tr then TLOAD else SLOAD) [a] [out]).inst_opcode /\
   (mk_inst id (if tr then TLOAD else SLOAD) [a] [out]).inst_opcode <> INVOKE`
    by (Cases_on `tr` >> simp[mk_inst_def, is_terminator_def]) >>
  drule_all straight_line_ptr_edge >>
  `step_prov PG G (mk_inst id (if tr then TLOAD else SLOAD) [a] [out])
      (update_var out (if tr then tload slot s else sload slot s) s) =
    DRESTRICT G (COMPL {out})` by
    (Cases_on `tr` >> simp[step_prov_def, out_prov_def, set_prov_def,
                           mk_inst_def]) >>
  `step_taint (mk_inst id (if tr then TLOAD else SLOAD) [a] [out]) s
      (update_var out (if tr then tload slot s else sload slot s) s) tn =
    tn with t_var := tn.t_var |+
      (out,key_taint (if tr then tn.t_trans else tn.t_stor) slot)` by
    (irule storage_load_payload_taint >> simp[update_var_def]) >>
  disch_then (qspec_then `PG` mp_tac) >>
  Cases_on `tr` >> simp[mk_inst_def, is_terminator_def] >>
  simp[GSYM mk_inst_def] >> strip_tac >>
  drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >>
  disch_then irule >>
  irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]
QED

Theorem storage_copy_store_step:
  eval_operand a s = SOME addr /\ eval_operand v s = SOME value ==>
  step_inst_base (mk_inst id MSTORE [a;v] []) s =
    OK (mstore (w2n addr) value s)
Proof
  strip_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_write2_def]
QED

Theorem storage_copy_store_ghost:
  eval_operand a s = SOME addr /\ eval_operand v s = SOME value ==>
  step_prov PG G (mk_inst id MSTORE [a;v] [])
    (mstore (w2n addr) value s) = G /\
  step_taint (mk_inst id MSTORE [a;v] []) s (mstore (w2n addr) value s) tn =
    tn with t_mem :=
      (tn.t_mem DIFF {i | w2n addr <= i /\ i < w2n addr + 32}) UNION
      {w2n addr + k | k IN op_taint tn v}
Proof
  strip_tac >>
  `new_site_bytes s (mstore (w2n addr) value s) = {}` by
    simp[new_site_bytes_def, mstore_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  simp[step_prov_def, mk_inst_def, step_taint_def, set_var_taint_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       fixed_source_write_range_def, written_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, range_bytes_def,
       taint_component_equality, mstore_def, EXTENSION,
       set_prov_def, DRESTRICT_UNIV]
QED

Theorem storage_copy_store_path_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MSTORE [Var p;v] []) /\
  eval_operand (Var p) s = SOME addr /\ eval_operand v s = SOME value /\
  ptr_covers G tn p s 32 /\ ~ctx_has_dalloca ctx ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G
    (tn with t_mem :=
      (tn.t_mem DIFF {i | w2n addr <= i /\ i < w2n addr + 32}) UNION
      {w2n addr + k | k IN op_taint tn v})
    (OK (mstore (w2n addr) value s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id MSTORE [Var p;v] []) s =
    OK (mstore (w2n addr) value s)` by simp[storage_copy_store_step] >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id MSTORE [Var p;v] []) s` by
    simp[ptr_inst_ok_mstore_payload] >>
  `~is_terminator (mk_inst id MSTORE [Var p;v] []).inst_opcode /\
   (mk_inst id MSTORE [Var p;v] []).inst_opcode <> INVOKE` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all straight_line_ptr_edge >>
  disch_then (qspec_then `PG` mp_tac) >>
  simp[mk_inst_def, is_terminator_def] >>
  simp[GSYM mk_inst_def, storage_copy_store_ghost] >> strip_tac >>
  drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >>
  disch_then irule >>
  irule (cj 1 gas_path_ptr_rules) >> simp[mstore_def]
QED

Theorem storage_copy_add_step:
  eval_operand left s = SOME a /\ eval_operand right s = SOME b ==>
  step_inst_base (mk_inst id ADD [left;right] [out]) s =
    OK (update_var out (a+b) s)
Proof
  strip_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def]
QED

Theorem storage_copy_add_path_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ADD [left;right] [out]) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  ~ctx_has_dalloca ctx ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id ADD [left;right] [out]) (update_var out (a+b) s))
    (tn with t_var := tn.t_var |+ (out,{}))
    (OK (update_var out (a+b) s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ADD [left;right] [out]) s =
    OK (update_var out (a+b) s)` by simp[storage_copy_add_step] >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id ADD [left;right] [out]) s` by
    (irule append_scalar_inst_check >> simp[update_var_def] >> metis_tac[]) >>
  `~is_terminator (mk_inst id ADD [left;right] [out]).inst_opcode /\
   (mk_inst id ADD [left;right] [out]).inst_opcode <> INVOKE` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all straight_line_ptr_edge >>
  disch_then (qspec_then `PG` mp_tac) >>
  simp[mk_inst_def, is_terminator_def] >>
  simp[GSYM mk_inst_def, scalar_add_taint, update_var_def] >>
  strip_tac >> drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >>
  disch_then irule >>
  irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]
QED

Theorem storage_copy_mul_step:
  eval_operand left s = SOME a /\ eval_operand right s = SOME b ==>
  step_inst_base (mk_inst id MUL [left;right] [out]) s =
    OK (update_var out (a*b) s)
Proof
  strip_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def]
QED

Theorem storage_copy_mul_path_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MUL [left;right] [out]) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  ~ctx_has_dalloca ctx ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {out})) (tn with t_var := tn.t_var |+ (out,{}))
    (OK (update_var out (a*b) s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id MUL [left;right] [out]) s =
    OK (update_var out (a*b) s)` by simp[storage_copy_mul_step] >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id MUL [left;right] [out]) s` by
    (irule typed_copy_loop_test_check >> simp[update_var_def] >> metis_tac[]) >>
  `~is_terminator (mk_inst id MUL [left;right] [out]).inst_opcode /\
   (mk_inst id MUL [left;right] [out]).inst_opcode <> INVOKE` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all straight_line_ptr_edge >>
  disch_then (qspec_then `PG` mp_tac) >>
  simp[mk_inst_def, is_terminator_def] >> simp[GSYM mk_inst_def] >>
  simp[typed_copy_loop_arith_ghost, update_var_def,
       step_prov_def, set_prov_def, out_prov_def, mk_inst_def] >>
  strip_tac >> drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >>
  disch_then irule >>
  irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]
QED

Theorem storage_copy_source_path_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++
    [mk_inst id ADD [src;Var cv] [sv];
     mk_inst (id+1) (if tr then TLOAD else SLOAD) [Var sv] [vv]] ++ post /\
  s.vs_inst_idx = LENGTH pre /\
  eval_operand src s = SOME a /\ lookup_var cv s = SOME (n2w k) /\
  op_taint tn src = {} /\ op_taint tn (Var cv) = {} /\
  ~ctx_has_dalloca ctx ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT
      (step_prov PG G (mk_inst id ADD [src;Var cv] [sv])
        (update_var sv (a+n2w k) s)) (COMPL {vv}))
    (tn with t_var := (tn.t_var |+ (sv,{})) |+
      (vv,key_taint (if tr then tn.t_trans else tn.t_stor) (a+n2w k)))
    (OK (update_var vv (if tr then tload (a+n2w k) s else sload (a+n2w k) s)
      (update_var sv (a+n2w k) s) with vs_inst_idx := s.vs_inst_idx+2))
Proof
  strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ADD [src;Var cv] [sv])` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  `eval_operand (Var cv) s = SOME (n2w k)` by simp[eval_operand_def] >>
  drule_all storage_copy_add_path_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 _` >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1)` >>
  `gas_path_ptr D 0 ctx fn PG G1 tn1 s1 0
    (DRESTRICT G1 (COMPL {vv}))
    (tn1 with t_var := tn1.t_var |+
      (vv,key_taint (if tr then tn1.t_trans else tn1.t_stor) (a+n2w k)))
    (OK (update_var vv (if tr then tload (a+n2w k) s1 else sload (a+n2w k) s1)
      s1 with vs_inst_idx := SUC s1.vs_inst_idx))` by
    (irule storage_copy_load_path_ptr >>
     simp[Abbr `s1`, Abbr `tn1`, update_var_def,
          get_instruction_def, EL_APPEND_EQN, ADD1,
          eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, op_taint_def] >>
     qexistsl [`Var sv`, `id+1`] >>
     simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  drule_all gas_path_ptr_then >>
  simp[Abbr `G1`, Abbr `tn1`, Abbr `s1`, update_var_def,
       sload_def, tload_def, contract_storage_def, contract_transient_def, ADD1]
QED

Theorem storage_copy_address_path_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ADD [Var root;offset] [out]) /\
  lookup_var root s = SOME a /\ eval_operand offset s = SOME (n2w off) /\
  ptr_covers G tn root s span /\ op_taint tn offset = {} /\
  off < span /\ off+width <= span /\ w2n a+off < dimword(:256) /\
  root <> out /\ ~ctx_has_dalloca ctx ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id ADD [Var root;offset] [out])
      (update_var out (a+n2w off) s))
    (tn with t_var := tn.t_var |+ (out,{}))
    (OK (update_var out (a+n2w off) s with vs_inst_idx := SUC s.vs_inst_idx)) /\
  ptr_covers
    (step_prov PG G (mk_inst id ADD [Var root;offset] [out])
      (update_var out (a+n2w off) s))
    (tn with t_var := tn.t_var |+ (out,{})) out
    (update_var out (a+n2w off) s with vs_inst_idx := SUC s.vs_inst_idx) width
Proof
  strip_tac >>
  `op_taint tn (Var root) = {}` by gvs[ptr_covers_def] >>
  conj_tac >-
    (irule storage_copy_add_path_ptr >> simp[eval_operand_def] >> metis_tac[]) >>
  `step_taint (mk_inst id ADD [Var root;offset] [out]) s
      (update_var out (a+n2w off) s) tn =
    tn with t_var := tn.t_var |+ (out,{})` by
    simp[scalar_add_taint, update_var_def] >>
  drule_all typed_copy_loop_dynamic_offset_covers >>
  disch_then (qspecl_then [`PG`, `id`] mp_tac) >>
  simp[]
QED

Theorem storage_copy_increment_path_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++
    [mk_inst id ADD [Var cv;Lit 1w] [nv];
     mk_inst (id+1) ASSIGN [Var nv] [cv]] ++ post /\
  s.vs_inst_idx = LENGTH pre /\
  lookup_var cv s = SOME (n2w k) /\ FLOOKUP G cv = NONE /\
  op_taint tn (Var cv) = {} /\ ~ctx_has_dalloca ctx ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {cv}))
    (tn with t_var := (tn.t_var |+ (nv,{})) |+ (cv,{}))
    (OK (update_var cv (n2w (k+1)) (update_var nv (n2w (k+1)) s)
      with vs_inst_idx := s.vs_inst_idx+2))
Proof
  strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ADD [Var cv;Lit 1w] [nv])` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  `eval_operand (Var cv) s = SOME (n2w k) /\
   eval_operand (Lit 1w) s = SOME 1w /\ op_taint tn (Lit 1w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all storage_copy_add_path_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] mp_tac) >>
  simp[step_prov_def, out_prov_def, first_prov_def, op_prov_def,
       set_prov_def, mk_inst_def, word_add_n2w] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1)` >>
  `gas_path_ptr D 0 ctx fn PG G1 tn1 s1 0
    (DRESTRICT G1 (COMPL {cv})) (tn1 with t_var := tn1.t_var |+ (cv,{}))
    (OK (update_var cv (n2w (k+1)) s1 with vs_inst_idx := SUC s1.vs_inst_idx))` by
    (irule copy_loop_scalar_assign_path_ptr >>
     simp[Abbr `s1`, Abbr `G1`, Abbr `tn1`, update_var_def,
          get_instruction_def, EL_APPEND_EQN, ADD1] >>
     qexistsl [`Var nv`, `id+1`] >>
     simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, op_taint_def,
          op_prov_def, FLOOKUP_DRESTRICT]) >>
  drule_all gas_path_ptr_then >>
  simp[Abbr `G1`, Abbr `tn1`, Abbr `s1`, update_var_def, ADD1]
QED

Theorem storage_copy_address_store_path_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++
    [mk_inst id ADD [Var root;offset] [out];
     mk_inst (id+1) MSTORE [Var out;Var vv] []] ++ post /\
  s.vs_inst_idx = LENGTH pre /\ lookup_var root s = SOME a /\
  eval_operand offset s = SOME (n2w off) /\ lookup_var vv s = SOME value /\
  ptr_covers G tn root s span /\ op_taint tn offset = {} /\
  off < span /\ off+32 <= span /\ w2n a+off < dimword(:256) /\
  root <> out /\ vv <> out /\ ~ctx_has_dalloca ctx ==>
  ?G1 tn1 t1.
    G1 = step_prov PG G (mk_inst id ADD [Var root;offset] [out])
      (update_var out (a+n2w off) s) /\
    tn1 = (tn with t_var := tn.t_var |+ (out,{})) /\
    t1 = (update_var out (a+n2w off) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G1
      (tn1 with t_mem :=
        (tn.t_mem DIFF {i | w2n (a+n2w off) <= i /\ i < w2n (a+n2w off)+32}) UNION
        {w2n (a+n2w off)+k | k IN op_taint tn (Var vv)})
      (OK (mstore (w2n (a+n2w off)) value t1 with vs_inst_idx := SUC t1.vs_inst_idx))
Proof
  strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ADD [Var root;offset] [out])` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  drule_all storage_copy_address_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK t1)` >>
  qexistsl [`G1`, `tn1`, `t1`] >>
  conj_tac >- simp[Abbr `G1`] >>
  conj_tac >- simp[Abbr `tn1`] >>
  conj_tac >- simp[Abbr `t1`] >>
  `gas_path_ptr D 0 ctx fn PG G1 tn1 t1 0 G1
    (tn1 with t_mem :=
      (tn1.t_mem DIFF {i | w2n (a+n2w off) <= i /\ i < w2n (a+n2w off)+32}) UNION
      {w2n (a+n2w off)+k | k IN op_taint tn1 (Var vv)})
    (OK (mstore (w2n (a+n2w off)) value t1 with vs_inst_idx := SUC t1.vs_inst_idx))` by
    (irule storage_copy_store_path_ptr >>
     simp[Abbr `t1`, Abbr `tn1`, update_var_def, get_instruction_def,
          EL_APPEND_EQN, ADD1, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
     conj_tac >- metis_tac[lookup_var_def] >>
     qexistsl [`id+1`, `out`] >>
     gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  drule_all gas_path_ptr_then >>
  simp[Abbr `G1`, Abbr `tn1`, Abbr `t1`, op_taint_def, FLOOKUP_UPDATE]
QED

Theorem storage_copy_store_taint_byte:
  bytes SUBSET {j | j < 32} /\ h < 32 ==>
  (b+32*k+h IN
    ((M DIFF {i | b+32*k <= i /\ i < b+32*k+32}) UNION
      {b+32*k+j | j IN bytes}) <=> h IN bytes) /\
  (!i. (i < b+32*k \/ b+32*k+32 <= i) ==>
    (i IN ((M DIFF {i | b+32*k <= i /\ i < b+32*k+32}) UNION
      {b+32*k+j | j IN bytes}) <=> i IN M))
Proof
  strip_tac >>
  simp[IN_UNION, IN_DIFF, GSPECIFICATION] >>
  gvs[SUBSET_DEF, GSPECIFICATION] >>
  rpt strip_tac >> eq_tac >> strip_tac >> gvs[] >>
  res_tac >> decide_tac
QED

Theorem storage_copy_payload_taint_advance:
  M' = (M DIFF {i | b+32*k <= i /\ i < b+32*k+32}) UNION
       {i | ?h. i = b+32*k+h /\ h IN key_taint X (a+n2w k)} /\
  (!j h. j < k /\ h < 32 ==>
     (b+32*j+h IN M <=> (a+n2w j,h) IN X)) /\
  (!i. (i < b \/ b+32*k <= i) ==> (i IN M <=> i IN M0)) ==>
  (!j h. j < k+1 /\ h < 32 ==>
     (b+32*j+h IN M' <=> (a+n2w j,h) IN X)) /\
  (!i. (i < b \/ b+32*(k+1) <= i) ==> (i IN M' <=> i IN M0))
Proof
  strip_tac >>
  `key_taint X (a+n2w k) SUBSET {j | j < 32}` by
    simp[key_taint_def, SUBSET_DEF] >>
  qpat_x_assum `M' = _` SUBST1_TAC >>
  conj_tac >-
    (rpt strip_tac >> Cases_on `j = k`
     >- (simp[IN_UNION, IN_DIFF, GSPECIFICATION, key_taint_def]) >>
     `j < k /\ b+32*j+h < b+32*k` by decide_tac >>
     simp[IN_UNION, IN_DIFF, GSPECIFICATION, key_taint_def] >>
     `~(?h'. b+(h+32*j) = b+(h'+32*k) /\ h' < 32 /\
          (a+n2w k,h') IN X)` by
       (strip_tac >> decide_tac) >>
     simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  `i < b+32*k \/ b+32*k+32 <= i` by decide_tac >>
  `i < b \/ b+32*k <= i` by decide_tac >>
  simp[IN_UNION, IN_DIFF, GSPECIFICATION, key_taint_def] >>
  `~(?h. i = b+(h+32*k) /\ h < 32 /\ (a+n2w k,h) IN X)` by
    (strip_tac >> decide_tac) >>
  gvs[] >> eq_tac >- (strip_tac >> gvs[] >> decide_tac) >> simp[]
QED

(* Chunk summaries attach the ordinary witness to the checked construction.
   No independent semantic execution is selected. *)
Theorem storage_copy_source_chunk_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++
    [mk_inst id ADD [src;Var cv] [sv];
     mk_inst (id+1) (if tr then TLOAD else SLOAD) [Var sv] [vv]] ++ post /\
  s.vs_inst_idx = LENGTH pre /\
  eval_operand src s = SOME a /\ lookup_var cv s = SOME (n2w k) /\
  op_taint tn src = {} /\ op_taint tn (Var cv) = {} /\
  ~ctx_has_dalloca ctx ==>
  ?G' tn' t u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    run_inst_seq
      [mk_inst id ADD [src;Var cv] [sv];
       mk_inst (id+1) (if tr then TLOAD else SLOAD) [Var sv] [vv]] s = OK u /\
    t = (u with vs_inst_idx := s.vs_inst_idx+2) /\
    lookup_var vv t = SOME (if tr then tload (a+n2w k) s else sload (a+n2w k) s) /\
    op_taint tn' (Var vv) = key_taint (if tr then tn.t_trans else tn.t_stor) (a+n2w k) /\
    copy_static t = copy_static s /\ t.vs_memory = s.vs_memory /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx+2 /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x <> sv /\ x <> vv ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all storage_copy_source_path_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t)` >>
  qexistsl [`G'`, `tn'`, `t`,
    `update_var vv (if tr then tload (a+n2w k) s else sload (a+n2w k) s)
      (update_var sv (a+n2w k) s)`] >>
  simp[] >> conj_tac >-
    (`step_inst_base (mk_inst id ADD [src;Var cv] [sv]) s =
       OK (update_var sv (a+n2w k) s)` by
       (irule storage_copy_add_step >> simp[eval_operand_def]) >>
     simp[run_inst_seq_def] >>
     `step_inst_base (mk_inst (id+1) (if tr then TLOAD else SLOAD)
        [Var sv] [vv]) (update_var sv (a+n2w k) s) =
       OK (update_var vv (if tr then tload (a+n2w k) s else sload (a+n2w k) s)
         (update_var sv (a+n2w k) s))` by
       (`eval_operand (Var sv) (update_var sv (a+n2w k) s) =
          SOME (a+n2w k)` by
          simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
        drule storage_copy_load_step >>
        disch_then (qspecl_then [`tr`, `vv`, `id+1`] mp_tac) >>
        simp[update_var_def, sload_def, tload_def,
             contract_storage_def, contract_transient_def]) >>
     simp[]) >>
  simp[Abbr `t`, Abbr `tn'`, Abbr `G'`, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, op_taint_def, copy_static_def,
       FLOOKUP_DRESTRICT, step_prov_other_output, mk_inst_def]
QED

Theorem storage_copy_store_chunk_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++
    [mk_inst id ADD [Var root;offset] [out];
     mk_inst (id+1) MSTORE [Var out;Var vv] []] ++ post /\
  s.vs_inst_idx = LENGTH pre /\ lookup_var root s = SOME a /\
  eval_operand offset s = SOME (n2w off) /\ lookup_var vv s = SOME value /\
  ptr_covers G tn root s span /\ op_taint tn offset = {} /\
  off < span /\ off+32 <= span /\ w2n a+off < dimword(:256) /\
  root <> out /\ vv <> out /\ ~ctx_has_dalloca ctx ==>
  ?G' tn' t u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    run_inst_seq [mk_inst id ADD [Var root;offset] [out];
      mk_inst (id+1) MSTORE [Var out;Var vv] []] s = OK u /\
    t = (u with vs_inst_idx := s.vs_inst_idx+2) /\
    copy_static t = copy_static s /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx+2 /\
    tn'.t_mem = (tn.t_mem DIFF
      {i | w2n (a+n2w off) <= i /\ i < w2n (a+n2w off)+32}) UNION
      {w2n (a+n2w off)+h | h IN op_taint tn (Var vv)} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x <> out ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all storage_copy_address_store_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn2 (OK t)` >>
  qexistsl [`G1`, `tn2`, `t`, `mstore (w2n (a+n2w off)) value
    (update_var out (a+n2w off) s)`] >>
  conj_tac >- simp[] >> conj_tac >-
    (`step_inst_base (mk_inst id ADD [Var root;offset] [out]) s =
       OK (update_var out (a+n2w off) s)` by
       (irule storage_copy_add_step >> simp[eval_operand_def]) >>
     `step_inst_base (mk_inst (id+1) MSTORE [Var out;Var vv] [])
        (update_var out (a+n2w off) s) =
       OK (mstore (w2n (a+n2w off)) value (update_var out (a+n2w off) s))` by
       (irule storage_copy_store_step >>
        simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
        metis_tac[lookup_var_def]) >>
     simp[run_inst_seq_def]) >>
  gvs[] >>
  simp[Abbr `t`, Abbr `tn2`, update_var_def, mstore_def, copy_static_def,
       lookup_var_def, FLOOKUP_UPDATE, op_taint_def,
       step_prov_other_output, mk_inst_def, ADD1]
QED

Theorem storage_copy_scale_chunk_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id MUL [Var cv;Lit 32w] [mv]) /\
  lookup_var cv s = SOME (n2w k) /\ op_taint tn (Var cv) = {} /\
  ~ctx_has_dalloca ctx ==>
  ?G' tn' t u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    run_inst_seq [mk_inst id MUL [Var cv;Lit 32w] [mv]] s = OK u /\
    t = (u with vs_inst_idx := s.vs_inst_idx+1) /\
    lookup_var mv t = SOME (n2w (32*k)) /\
    FLOOKUP G' mv = NONE /\ op_taint tn' (Var mv) = {} /\
    copy_static t = copy_static s /\ t.vs_memory = s.vs_memory /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx+1 /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x <> mv ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `eval_operand (Var cv) s = SOME (n2w k) /\
   eval_operand (Lit 32w) s = SOME 32w /\ op_taint tn (Lit 32w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all storage_copy_mul_path_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t)` >>
  qexistsl [`G'`, `tn'`, `t`, `update_var mv (n2w k * 32w) s`] >>
  conj_tac >- simp[] >> conj_tac >-
    (`step_inst_base (mk_inst id MUL [Var cv;Lit 32w] [mv]) s =
      OK (update_var mv (n2w k * 32w) s)` by simp[storage_copy_mul_step] >>
     simp[run_inst_seq_def]) >>
  simp[Abbr `t`, Abbr `tn'`, Abbr `G'`, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def, copy_static_def,
       word_mul_n2w, ADD1] >> simp[Once MULT_COMM]
QED

Theorem storage_copy_increment_chunk_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++
    [mk_inst id ADD [Var cv;Lit 1w] [nv];
     mk_inst (id+1) ASSIGN [Var nv] [cv]] ++ post /\
  s.vs_inst_idx = LENGTH pre /\
  lookup_var cv s = SOME (n2w k) /\ FLOOKUP G cv = NONE /\
  op_taint tn (Var cv) = {} /\ ~ctx_has_dalloca ctx ==>
  ?G' tn' t u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    run_inst_seq [mk_inst id ADD [Var cv;Lit 1w] [nv];
      mk_inst (id+1) ASSIGN [Var nv] [cv]] s = OK u /\
    t = (u with vs_inst_idx := s.vs_inst_idx+2) /\
    lookup_var cv t = SOME (n2w (k+1)) /\
    FLOOKUP G' cv = NONE /\ op_taint tn' (Var cv) = {} /\
    copy_static t = copy_static s /\ t.vs_memory = s.vs_memory /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx+2 /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x <> nv /\ x <> cv ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all storage_copy_increment_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t)` >>
  qexistsl [`G'`, `tn'`, `t`,
    `update_var cv (n2w (k+1)) (update_var nv (n2w (k+1)) s)`] >>
  conj_tac >- simp[] >> conj_tac >-
    (`step_inst_base (mk_inst id ADD [Var cv;Lit 1w] [nv]) s =
       OK (update_var nv (n2w (k+1)) s)` by
       (simp[GSYM word_add_n2w] >> irule storage_copy_add_step >>
        simp[eval_operand_def]) >>
     `step_inst_base (mk_inst (id+1) ASSIGN [Var nv] [cv])
       (update_var nv (n2w (k+1)) s) =
       OK (update_var cv (n2w (k+1)) (update_var nv (n2w (k+1)) s))` by
       (irule copy_loop_scalar_assign_step >>
        simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
     simp[run_inst_seq_def]) >>
  simp[Abbr `t`, Abbr `tn'`, Abbr `G'`, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def, copy_static_def]
QED

Theorem run_inst_seq_cursor_append:
  run_inst_seq code s = OK u /\ t = (u with vs_inst_idx := i) /\
  run_inst_seq more t = OK v /\ t' = (v with vs_inst_idx := j) /\
  EVERY (\inst. ~is_terminator inst.inst_opcode) more ==>
  ?w. run_inst_seq (code ++ more) s = OK w /\
      t' = (w with vs_inst_idx := j)
Proof
  strip_tac >> gvs[] >>
  qpat_assum `run_inst_seq code s = OK u`
    (mp_then Any (qspec_then `more` assume_tac) run_inst_seq_append) >>
  drule run_inst_seq_inst_idx >>
  disch_then (qspecl_then [`u`, `i`] mp_tac) >>
  Cases_on `run_inst_seq more u` >>
  gvs[instIdxIndepTheory.exec_result_map_def, run_inst_seq_append] >> metis_tac[]
QED

Theorem storage_copy_destination_chunk_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++
    [mk_inst id MUL [Var cv;Lit 32w] [mv];
     mk_inst (id+1) ADD [Var root;Var mv] [dv];
     mk_inst (id+2) MSTORE [Var dv;Var vv] []] ++ post /\
  s.vs_inst_idx = LENGTH pre /\ lookup_var root s = SOME a /\
  lookup_var cv s = SOME (n2w k) /\ lookup_var vv s = SOME value /\
  ptr_covers G tn root s span /\ op_taint tn (Var cv) = {} /\
  32*k+32 <= span /\ w2n a+32*k < dimword(:256) /\
  ALL_DISTINCT [root;cv;vv;mv;dv] /\ ~ctx_has_dalloca ctx ==>
  ?G' tn' t u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    run_inst_seq
      [mk_inst id MUL [Var cv;Lit 32w] [mv];
       mk_inst (id+1) ADD [Var root;Var mv] [dv];
       mk_inst (id+2) MSTORE [Var dv;Var vv] []] s = OK u /\
    t = (u with vs_inst_idx := s.vs_inst_idx+3) /\
    copy_static t = copy_static s /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx+3 /\
    tn'.t_mem = (tn.t_mem DIFF
      {i | w2n (a+n2w (32*k)) <= i /\ i < w2n (a+n2w (32*k))+32}) UNION
      {w2n (a+n2w (32*k))+h | h IN op_taint tn (Var vv)} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x <> mv /\ x <> dv ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id MUL [Var cv;Lit 32w] [mv])` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  drule_all storage_copy_scale_chunk_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK t1)` >>
  `~t1.vs_halted /\ lookup_var root t1 = SOME a /\
   lookup_var vv t1 = SOME value /\ ptr_covers G1 tn1 root t1 span` by
    (drule copy_static_fields >> strip_tac >>
     gvs[ALL_DISTINCT, ptr_covers_def, lookup_var_def] >> metis_tac[]) >>
  `?G2 tn2 t2 u2.
    gas_path_ptr D 0 ctx fn PG G1 tn1 t1 0 G2 tn2 (OK t2) /\
    run_inst_seq [mk_inst (id+1) ADD [Var root;Var mv] [dv];
      mk_inst ((id+1)+1) MSTORE [Var dv;Var vv] []] t1 = OK u2 /\
    t2 = (u2 with vs_inst_idx := t1.vs_inst_idx+2) /\
    copy_static t2 = copy_static t1 /\
    t2.vs_current_bb = t1.vs_current_bb /\ t2.vs_inst_idx = t1.vs_inst_idx+2 /\
    tn2.t_mem = (tn1.t_mem DIFF
      {i | w2n (a+n2w (32*k)) <= i /\ i < w2n (a+n2w (32*k))+32}) UNION
      {w2n (a+n2w (32*k))+h | h IN op_taint tn1 (Var vv)} /\
    tn2.t_stor = tn1.t_stor /\ tn2.t_trans = tn1.t_trans /\ tn2.t_imm = tn1.t_imm /\
    (!x. x <> dv ==> lookup_var x t2 = lookup_var x t1 /\
      FLOOKUP G2 x = FLOOKUP G1 x /\ op_taint tn2 (Var x) = op_taint tn1 (Var x))` by
    (irule storage_copy_store_chunk_ptr >>
     fs[ALL_DISTINCT] >> simp[eval_operand_def] >>
     conj_tac >-
       (qexistsl [`post`, `pre ++ [mk_inst id MUL [Var cv;Lit 32w] [mv]]`] >>
        simp[APPEND_ASSOC]) >>
     conj_tac >- gvs[lookup_var_def] >>
     qexists `span` >> gvs[ptr_covers_def, lookup_var_def] >> decide_tac) >>
  suspend "assemble"
QED

Resume storage_copy_destination_chunk_ptr[assemble]:
  `EVERY (\inst. ~is_terminator inst.inst_opcode)
    [mk_inst (id+1) ADD [Var root;Var mv] [dv];
     mk_inst ((id+1)+1) MSTORE [Var dv;Var vv] []]` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_cursor_append >> strip_tac >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  qexistsl [`G2`, `tn2`, `w`] >>
  simp[] >>
  `op_taint tn1 (Var vv) = op_taint tn (Var vv)` by
    (fs[ALL_DISTINCT] >> metis_tac[]) >>
  fs[] >> conj_tac >- (gvs[] >> simp[]) >>
  gvs[lookup_var_def] >> metis_tac[]
QED
Finalise storage_copy_destination_chunk_ptr

Theorem storage_copy_body_path_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++
    [mk_inst id ADD [src;Var cv] [sv];
     mk_inst (id+1) (if tr then TLOAD else SLOAD) [Var sv] [vv];
     mk_inst (id+2) MUL [Var cv;Lit 32w] [mv];
     mk_inst (id+3) ADD [Var root;Var mv] [dv];
     mk_inst (id+4) MSTORE [Var dv;Var vv] [];
     mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
     mk_inst (id+6) ASSIGN [Var nv] [cv]] ++ post /\
  s.vs_inst_idx = LENGTH pre /\
  eval_operand src s = SOME a /\ lookup_var root s = SOME b /\
  lookup_var cv s = SOME (n2w k) /\ FLOOKUP G cv = NONE /\
  op_taint tn src = {} /\ op_taint tn (Var cv) = {} /\
  ptr_covers G tn root s span /\ 32*k+32 <= span /\
  w2n b+32*k < dimword(:256) /\
  ALL_DISTINCT [root;cv;sv;vv;mv;dv;nv] /\
  (!x. MEM x [cv;sv;vv;mv;dv;nv] ==> src <> Var x) /\
  ~ctx_has_dalloca ctx ==>
  ?G' tn' t u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    run_inst_seq
      [mk_inst id ADD [src;Var cv] [sv];
       mk_inst (id+1) (if tr then TLOAD else SLOAD) [Var sv] [vv];
       mk_inst (id+2) MUL [Var cv;Lit 32w] [mv];
       mk_inst (id+3) ADD [Var root;Var mv] [dv];
       mk_inst (id+4) MSTORE [Var dv;Var vv] [];
       mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
       mk_inst (id+6) ASSIGN [Var nv] [cv]] s = OK u /\
    t = (u with vs_inst_idx := s.vs_inst_idx+7) /\
    lookup_var root t = SOME b /\ ptr_covers G' tn' root t span /\
    eval_operand src t = SOME a /\ op_taint tn' src = {} /\
    lookup_var cv t = SOME (n2w (k+1)) /\
    FLOOKUP G' cv = NONE /\ op_taint tn' (Var cv) = {} /\
    copy_static t = copy_static s /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx+7 /\
    tn'.t_mem = (tn.t_mem DIFF
      {i | w2n (b+n2w (32*k)) <= i /\ i < w2n (b+n2w (32*k))+32}) UNION
      {i | ?h. i = w2n (b+n2w (32*k))+h /\
        h IN key_taint (if tr then tn.t_trans else tn.t_stor) (a+n2w k)} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. ~MEM x [cv;sv;vv;mv;dv;nv] ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `bb.bb_instructions = pre ++
    [mk_inst id ADD [src;Var cv] [sv];
     mk_inst (id+1) (if tr then TLOAD else SLOAD) [Var sv] [vv]] ++
    ([mk_inst (id+2) MUL [Var cv;Lit 32w] [mv];
      mk_inst (id+3) ADD [Var root;Var mv] [dv];
      mk_inst (id+4) MSTORE [Var dv;Var vv] [];
      mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
      mk_inst (id+6) ASSIGN [Var nv] [cv]] ++ post)` by simp[] >>
  drule_all storage_copy_source_chunk_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK t1)` >>
  `?G2 tn2 t2 u2.
    gas_path_ptr D 0 ctx fn PG G1 tn1 t1 0 G2 tn2 (OK t2) /\
    run_inst_seq
      [mk_inst (id+2) MUL [Var cv;Lit 32w] [mv];
       mk_inst ((id+2)+1) ADD [Var root;Var mv] [dv];
       mk_inst ((id+2)+2) MSTORE [Var dv;Var vv] []] t1 = OK u2 /\
    t2 = (u2 with vs_inst_idx := t1.vs_inst_idx+3) /\
    copy_static t2 = copy_static t1 /\
    t2.vs_current_bb = t1.vs_current_bb /\ t2.vs_inst_idx = t1.vs_inst_idx+3 /\
    tn2.t_mem = (tn1.t_mem DIFF
      {i | w2n (b+n2w (32*k)) <= i /\ i < w2n (b+n2w (32*k))+32}) UNION
      {w2n (b+n2w (32*k))+h | h IN op_taint tn1 (Var vv)} /\
    tn2.t_stor = tn1.t_stor /\ tn2.t_trans = tn1.t_trans /\ tn2.t_imm = tn1.t_imm /\
    (!x. x <> mv /\ x <> dv ==> lookup_var x t2 = lookup_var x t1 /\
      FLOOKUP G2 x = FLOOKUP G1 x /\ op_taint tn2 (Var x) = op_taint tn1 (Var x))`
    by suspend "destination" >>
  suspend "increment_and_assemble"
QED

Resume storage_copy_body_path_ptr[destination]:
  `~t1.vs_halted /\ lookup_var root t1 = SOME b /\
   lookup_var cv t1 = SOME (n2w k) /\ op_taint tn1 (Var cv) = {} /\
   ptr_covers G1 tn1 root t1 span` by
    (drule copy_static_fields >> strip_tac >>
     gvs[ALL_DISTINCT, ptr_covers_def, lookup_var_def] >> metis_tac[]) >>
  irule storage_copy_destination_chunk_ptr >>
  fs[ALL_DISTINCT] >> simp[] >>
  conj_tac >-
    (qexistsl [`[mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
                mk_inst (id+6) ASSIGN [Var nv] [cv]] ++ post`,
              `pre ++ [mk_inst id ADD [src;Var cv] [sv];
                mk_inst (id+1) (if tr then TLOAD else SLOAD) [Var sv] [vv]]`] >>
     simp[APPEND_ASSOC]) >>
  qexists `span` >> gvs[ptr_covers_def, lookup_var_def]
QED
Resume storage_copy_body_path_ptr[increment_and_assemble]:
  `~t2.vs_halted /\ lookup_var cv t2 = SOME (n2w k) /\
   FLOOKUP G2 cv = NONE /\ op_taint tn2 (Var cv) = {}` by
    (qpat_assum `copy_static t2 = copy_static t1`
       (mp_then Any strip_assume_tac copy_static_fields) >>
     qpat_assum `copy_static t1 = copy_static s`
       (mp_then Any strip_assume_tac copy_static_fields) >>
     fs[ALL_DISTINCT] >> metis_tac[]) >>
  `?G3 tn3 t3 u3.
    gas_path_ptr D 0 ctx fn PG G2 tn2 t2 0 G3 tn3 (OK t3) /\
    run_inst_seq [mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
      mk_inst ((id+5)+1) ASSIGN [Var nv] [cv]] t2 = OK u3 /\
    t3 = (u3 with vs_inst_idx := t2.vs_inst_idx+2) /\
    lookup_var cv t3 = SOME (n2w (k+1)) /\
    FLOOKUP G3 cv = NONE /\ op_taint tn3 (Var cv) = {} /\
    copy_static t3 = copy_static t2 /\ t3.vs_memory = t2.vs_memory /\
    t3.vs_current_bb = t2.vs_current_bb /\ t3.vs_inst_idx = t2.vs_inst_idx+2 /\
    tn3.t_mem = tn2.t_mem /\ tn3.t_stor = tn2.t_stor /\
    tn3.t_trans = tn2.t_trans /\ tn3.t_imm = tn2.t_imm /\
    (!x. x <> nv /\ x <> cv ==> lookup_var x t3 = lookup_var x t2 /\
      FLOOKUP G3 x = FLOOKUP G2 x /\ op_taint tn3 (Var x) = op_taint tn2 (Var x))` by
    (irule storage_copy_increment_chunk_ptr >> simp[] >>
     qexistsl [`post`, `pre ++
       [mk_inst id ADD [src;Var cv] [sv];
        mk_inst (id+1) (if tr then TLOAD else SLOAD) [Var sv] [vv];
        mk_inst (id+2) MUL [Var cv;Lit 32w] [mv];
        mk_inst (id+3) ADD [Var root;Var mv] [dv];
        mk_inst (id+4) MSTORE [Var dv;Var vv] []]`] >> simp[APPEND_ASSOC]) >>
  suspend "assemble_body"
QED
Resume storage_copy_body_path_ptr[assemble_body]:
  `EVERY (\inst. ~is_terminator inst.inst_opcode)
    [mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
     mk_inst ((id+5)+1) ASSIGN [Var nv] [cv]]` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_cursor_append >> strip_tac >>
  qpat_x_assum `run_inst_seq [mk_inst (id+5) ADD _ _; _] _ = _` kall_tac >>
  qpat_x_assum `run_inst_seq [mk_inst (id+2) MUL _ _; _; _] _ = _` kall_tac >>
  `EVERY (\inst. ~is_terminator inst.inst_opcode)
    ([mk_inst (id+2) MUL [Var cv;Lit 32w] [mv];
      mk_inst ((id+2)+1) ADD [Var root;Var mv] [dv];
      mk_inst ((id+2)+2) MSTORE [Var dv;Var vv] []] ++
     [mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
      mk_inst ((id+5)+1) ASSIGN [Var nv] [cv]])` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_cursor_append >> strip_tac >>
  drule_all gas_path_ptr_then >> disch_then (assume_tac o SRULE []) >>
  qpat_x_assum `gas_path_ptr D 0 ctx fn PG G2 tn2 t2 0 _ _ _` kall_tac >>
  qpat_x_assum `gas_path_ptr D 0 ctx fn PG G1 tn1 t1 0 G2 tn2 _` kall_tac >>
  drule_all gas_path_ptr_then >> disch_then (assume_tac o SRULE []) >>
  suspend "body_frames"
QED
Resume storage_copy_body_path_ptr[body_frames]:
  `lookup_var root t3 = lookup_var root s /\
   FLOOKUP G3 root = FLOOKUP G root /\
   op_taint tn3 (Var root) = op_taint tn (Var root)` by
    (qpat_x_assum `t1 = _` kall_tac >>
     qpat_x_assum `t2 = _` kall_tac >>
     rpt (qpat_x_assum `t3 = _` kall_tac) >> fs[ALL_DISTINCT] >> simp[]) >>
  `ptr_covers G3 tn3 root t3 span` by
    (qpat_x_assum `t1 = _` kall_tac >> qpat_x_assum `t2 = _` kall_tac >>
     rpt (qpat_x_assum `t3 = _` kall_tac) >> fs[ptr_covers_def]) >>
  `eval_operand src t3 = SOME a /\ op_taint tn3 src = {}` by
    (qpat_x_assum `t1 = _` kall_tac >> qpat_x_assum `t2 = _` kall_tac >>
     rpt (qpat_x_assum `t3 = _` kall_tac) >>
     qpat_assum `copy_static t3 = copy_static t2`
       (mp_then Any strip_assume_tac copy_static_fields) >>
     qpat_assum `copy_static t2 = copy_static t1`
       (mp_then Any strip_assume_tac copy_static_fields) >>
     qpat_assum `copy_static t1 = copy_static s`
       (mp_then Any strip_assume_tac copy_static_fields) >>
     Cases_on `src` >> fs[eval_operand_def, op_taint_def,
       DISJ_IMP_THM, FORALL_AND_THM, lookup_var_def] >> simp[]) >>
  qexistsl [`G3`, `tn3`, `t3`, `w'`] >> simp[] >>
  fs[] >> simp[EXTENSION, GSPECIFICATION]
QED
Finalise storage_copy_body_path_ptr

(* Semantic and ghost preservation consume the very runtime witness exported
   by storage_copy_body_path_ptr, never an independently selected execution. *)
Theorem storage_copy_body_invariant_advance:
  run_inst_seq
    [mk_inst id ADD [src;Var cv] [sv];
     mk_inst (id+1) (if tr then TLOAD else SLOAD) [Var sv] [vv];
     mk_inst (id+2) MUL [Var cv;Lit 32w] [mv];
     mk_inst (id+3) ADD [Var root;Var mv] [dv];
     mk_inst (id+4) MSTORE [Var dv;Var vv] [];
     mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
     mk_inst (id+6) ASSIGN [Var nv] [cv]] s = OK u /\
  t = (u with vs_inst_idx := j) /\
  eval_operand src s = SOME a /\ lookup_var root s = SOME b /\
  lookup_var cv s = SOME (n2w k) /\
  ALL_DISTINCT [root;cv;sv;vv;mv;dv;nv] /\
  (!x. MEM x [cv;sv;vv;mv;dv;nv] ==> src <> Var x) /\
  copy_prefix (if tr then LocTransient else LocStorage) a (w2n b) n sbase k s /\
  k < n /\ w2n b+32*n < dimword(:256) /\
  tn'.t_mem = (tn.t_mem DIFF
    {i | w2n (b+n2w (32*k)) <= i /\ i < w2n (b+n2w (32*k))+32}) UNION
    {i | ?h. i = w2n (b+n2w (32*k))+h /\
      h IN key_taint (if tr then tn.t_trans else tn.t_stor) (a+n2w k)} /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
  (!i h. i < k /\ h < 32 ==>
     (w2n b+32*i+h IN tn.t_mem <=>
      (a+n2w i,h) IN (if tr then tn.t_trans else tn.t_stor))) /\
  (!i. (i < w2n b \/ w2n b+32*k <= i) ==> (i IN tn.t_mem <=> i IN M0)) ==>
  copy_prefix (if tr then LocTransient else LocStorage) a (w2n b) n sbase (k+1) t /\
  (!i h. i < k+1 /\ h < 32 ==>
     (w2n b+32*i+h IN tn'.t_mem <=>
      (a+n2w i,h) IN (if tr then tn'.t_trans else tn'.t_stor))) /\
  (!i. (i < w2n b \/ w2n b+32*(k+1) <= i) ==> (i IN tn'.t_mem <=> i IN M0))
Proof
  strip_tac >>
  `k < dimword(:256)` by decide_tac >> conj_tac >-
    (gvs[] >> Cases_on `tr` >> gvs[copy_prefix_idx]
     >- (drule_at (Pat `run_inst_seq _ _ = OK _`)
           (SRULE [] (Q.INST [`loc` |-> `LocTransient`] storage_copy_body_prefix)) >>
         simp[eval_operand_def, ALL_DISTINCT, GSYM dimword_def] >>
         disch_then irule >> fs[dimword_def] >>
         `k < 2**256` by (simp[] >> decide_tac) >> simp[] >> metis_tac[]) >>
     drule_at (Pat `run_inst_seq _ _ = OK _`)
       (SRULE [] (Q.INST [`loc` |-> `LocStorage`] storage_copy_body_prefix)) >>
     simp[eval_operand_def, ALL_DISTINCT, GSYM dimword_def] >>
     disch_then irule >> fs[dimword_def] >>
         `k < 2**256` by (simp[] >> decide_tac) >> simp[] >> metis_tac[]) >>
  `w2n (b+n2w (32*k)) = w2n b+32*k` by
    (`32*k < dimword(:256) /\ w2n b+32*k < dimword(:256)` by decide_tac >>
     simp[w2n_add_2, w2n_n2w]) >>
  qpat_x_assum `tn'.t_stor = _` SUBST1_TAC >>
  qpat_x_assum `tn'.t_trans = _` SUBST1_TAC >>
  irule storage_copy_payload_taint_advance >>
  qexists `tn.t_mem` >> simp[] >> fs[]
QED

Theorem storage_copy_backedge_path_ptr:
  gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
  ~t.vs_halted /\ lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME (mk_inst id JMP [Label hdr] []) /\
  ~ctx_has_dalloca ctx /\
  copy_prefix loc a b n sbase k t /\ ptr_covers G' tn' root t span ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK (jump_to hdr t)) /\
  copy_prefix loc a b n sbase k (jump_to hdr t) /\
  ptr_covers G' tn' root (jump_to hdr t) span /\
  copy_static (jump_to hdr t) = copy_static t /\
  eval_operand src (jump_to hdr t) = eval_operand src t /\
  (!x. lookup_var x (jump_to hdr t) = lookup_var x t)
Proof
  strip_tac >>
  `gas_path_ptr D 0 ctx fn PG G' tn' t 0 G' tn' (OK (jump_to hdr t))` by
    (irule copy_loop_jump_path_ptr >> simp[mk_inst_def, op_taint_def] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[instruction_accessors, instruction_accfupds,
                     combinTheory.K_THM, opcode_case_def] >> simp[]) >>
  conj_tac >- (drule_all gas_path_ptr_then >> simp[]) >>
  simp[copy_prefix_jump, ptr_covers_def, copy_static_def, jump_to_def,
       lookup_var_def] >> fs[ptr_covers_def, lookup_var_def]
QED
