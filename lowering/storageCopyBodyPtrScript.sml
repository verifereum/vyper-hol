(* Counted fixed-instruction boundaries for the storage-copy body.
   Arbitrary payload taint is retained at the actual checked endpoint. *)
Theory storageCopyBodyPtr
Ancestors
  storageCopyControlPtr typedCopyLoopHeaderPtr payloadLoadStorePtr
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
