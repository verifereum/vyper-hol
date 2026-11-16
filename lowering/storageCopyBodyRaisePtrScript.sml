(* Exact taint transport for storage/transient word copies. Payload taint
   is allowed; only address and counter operands must remain clean. *)
Theory storageCopyBodyRaisePtr
Ancestors
  storageCopyControlRaisePtr fragGasSeqPtr fragGasPathPtr ptrDiscipline ptrSafeRun codegenRel contextCodegenRel
  venomState venomInst finite_map pred_set words fragExecPtr memLocDefs

Theorem storage_copy_load_taint:
  eval_operand src s = SOME slot /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
  step_taint (mk_inst id (if tr then TLOAD else SLOAD) [src] [out]) s s' tn =
    tn with t_var := tn.t_var |+
      (out,key_taint (if tr then tn.t_trans else tn.t_stor) slot)
Proof
  strip_tac >>
  `new_site_bytes s s' = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  Cases_on `tr` >>
  gvs[step_taint_def, set_var_taint_def, mk_inst_def, out_taint_def,
      mem_taint_def, step_writes_def, source_memory_write_ranges_def,
      written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
      range_bytes_def, taint_component_equality, DRESTRICT_UNIV]
QED

(* Byte offsets are unchanged, not endian-reversed. key_taint already
   intersects source taint with the 32-byte word interval. *)
Theorem storage_copy_store_written_taint:
  eval_operand dst s = SOME addr /\
  op_taint tn value = key_taint X slot ==>
  written_taint tn (mk_inst id MSTORE [dst;value] []) s =
    {w2n addr + r | r < 32 /\ (slot,r) IN X}
Proof
  simp[written_taint_def, mk_inst_def, key_taint_def]
QED

Theorem storage_copy_store_mem_taint:
  eval_operand dst s = SOME addr /\ eval_operand value s = SOME w /\
  op_taint tn value = key_taint X slot /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
  mem_taint tn (mk_inst id MSTORE [dst;value] []) s s' =
    (tn.t_mem DIFF {x | w2n addr <= x /\ x < w2n addr + 32}) UNION
    {w2n addr + r | r < 32 /\ (slot,r) IN X}
Proof
  strip_tac >>
  `new_site_bytes s s' = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  simp[mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, key_taint_def,
       mk_inst_def, fixed_source_write_range_def, range_bytes_def] >>
  simp[EXTENSION]
QED

Theorem storage_copy_payload_byte_probe:
  key_taint {(17w:bytes32,7:num)} 17w = {7} /\
  written_taint (tn with t_var := tn.t_var |+ ("payload",{7}))
    (mk_inst 0 MSTORE [Lit 0w; Var "payload"] []) s = {7}
Proof
  simp[key_taint_def, written_taint_def, mk_inst_def, eval_operand_def,
       op_taint_def, FLOOKUP_UPDATE, EXTENSION]
QED

Theorem storage_copy_mstore_check:
  ptr_covers G tn p s 32 /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id MSTORE [Var p; value] []) s
Proof
  strip_tac >> gvs[bodyPtrDefsTheory.ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, fixed_source_write_range_def,
       eval_operand_def] >>
  conj_tac
  >- (Cases_on `eval_operand value s` >> simp[] >>
      rpt strip_tac >> gvs[] >> simp[mem_write_ops_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
  asm_simp_tac bool_ss [venomExecSemanticsTheory.step_inst_base_opcode_eqs, instruction_accessors, instruction_accfupds, opcode_case_def, combinTheory.K_THM] >>
  simp[venomExecSemanticsTheory.exec_write2_def, eval_operand_def,
       AllCaseEqs(), mstore_def] >> rpt strip_tac >> gvs[]
QED

Theorem storage_copy_load_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id (if tr then TLOAD else SLOAD) [src] [out]) /\
  eval_operand src s = SOME slot /\ op_taint tn src = {} ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+
      (out,key_taint (if tr then tn.t_trans else tn.t_stor) slot))
    (OK (update_var out (if tr then tload slot s else sload slot s) s
      with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  qabbrev_tac `i = mk_inst id (if tr then TLOAD else SLOAD) [src] [out]` >>
  qabbrev_tac `u = update_var out (if tr then tload slot s else sload slot s) s` >>
  `step_inst_base i s = OK u` by
    (unabbrev_all_tac >> Cases_on `tr` >>
     simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs, mk_inst_def, venomExecSemanticsTheory.exec_read1_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >> Cases_on `tr` >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
          mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, venomExecSemanticsTheory.step_inst_non_invoke] >>
     gvs[Abbr `u`, update_var_def] >> metis_tac[]) >>
  `step_prov PG G i u = DRESTRICT G (COMPL {out})` by
    (Cases_on `tr` >> simp[Abbr `i`, step_prov_def, set_prov_def,
                            out_prov_def, mk_inst_def]) >>
  `step_taint i s u tn = tn with t_var := tn.t_var |+
     (out,key_taint (if tr then tn.t_trans else tn.t_stor) slot)` by
    (simp[Abbr `i`] >> irule storage_copy_load_taint >> simp[Abbr `u`, update_var_def]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+
      (out,key_taint (if tr then tn.t_trans else tn.t_stor) slot))
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
     Cases_on `tr` >> gvs[Abbr `i`, mk_inst_def, is_terminator_def] >> metis_tac[]) >>
  drule (cj 2 gas_path_ptr_rules) >> simp[] >> disch_then irule >>
  irule (cj 1 gas_path_ptr_rules) >> simp[Abbr `u`, update_var_def]
QED

Theorem storage_copy_mstore_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MSTORE [Var dst;value] []) /\
  lookup_var dst s = SOME addr /\ eval_operand value s = SOME w /\
  ptr_covers G tn dst s 32 ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G
    (step_taint (mk_inst id MSTORE [Var dst;value] []) s
      (mstore (w2n addr) w s) tn)
    (OK (mstore (w2n addr) w s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id MSTORE [Var dst;value] []) s =
     OK (mstore (w2n addr) w s)` by
    (simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs, mk_inst_def, venomExecSemanticsTheory.exec_write2_def, eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id MSTORE [Var dst;value] []) s` by
    (irule storage_copy_mstore_check >> simp[]) >>
  `step_prov PG G (mk_inst id MSTORE [Var dst;value] []) (mstore (w2n addr) w s) = G` by
    simp[step_prov_def, set_prov_def, mk_inst_def, DRESTRICT_UNIV] >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G
    (step_taint (mk_inst id MSTORE [Var dst;value] []) s
      (mstore (w2n addr) w s) tn)
    (OK (mstore (w2n addr) w s with vs_inst_idx := SUC s.vs_inst_idx))` by
    (drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
     gvs[mk_inst_def, is_terminator_def] >> metis_tac[]) >>
  drule (cj 2 gas_path_ptr_rules) >> simp[] >> disch_then irule >>
  irule (cj 1 gas_path_ptr_rules) >>
  simp[mstore_def, write_memory_with_expansion_def]
QED

Theorem storage_copy_mstore_ghost:
  eval_operand (Var dst) s = SOME addr /\ eval_operand value s = SOME w /\
  op_taint tn value = key_taint X slot ==>
  step_taint (mk_inst id MSTORE [Var dst;value] []) s
    (mstore (w2n addr) w s) tn =
  tn with t_mem :=
    (tn.t_mem DIFF {x | w2n addr <= x /\ x < w2n addr + 32}) UNION
    {w2n addr + r | r < 32 /\ (slot,r) IN X}
Proof
  strip_tac >>
  `mem_taint tn (mk_inst id MSTORE [Var dst;value] []) s
     (mstore (w2n addr) w s) =
    (tn.t_mem DIFF {x | w2n addr <= x /\ x < w2n addr + 32}) UNION
    {w2n addr + r | r < 32 /\ (slot,r) IN X}` by
    (irule storage_copy_store_mem_taint >>
     simp[mstore_def, write_memory_with_expansion_def] >> metis_tac[]) >>
  simp[step_taint_def, set_var_taint_def, mk_inst_def,
       store_taint_def, adopt_reset_def, imm_taint_def,
       taint_component_equality, DRESTRICT_UNIV]
QED

(* The loop's final ASSIGN transports the clean scalar counter, not payload. *)
Theorem storage_copy_counter_assign_ghost:
  op_prov G (Var nv) = NONE /\ op_taint tn (Var nv) = {} /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
  step_prov PG G (mk_inst id ASSIGN [Var nv] [cv]) s' =
    DRESTRICT G (COMPL {cv}) /\
  step_taint (mk_inst id ASSIGN [Var nv] [cv]) s s' tn =
    tn with t_var := tn.t_var |+ (cv,{})
Proof
  strip_tac >>
  `new_site_bytes s s' = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       set_var_taint_def, mk_inst_def, op_taint_def, op_prov_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       range_bytes_def, taint_component_equality, DRESTRICT_UNIV,
       out_taint_def, first_prov_def] >> gvs[op_prov_def, op_taint_def] >>
  Cases_on `eval_operand (Var nv) s` >> simp[]
QED

Theorem storage_copy_counter_assign_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSIGN [Var nv] [cv]) /\
  lookup_var nv s = SOME w /\
  op_prov G (Var nv) = NONE /\ op_taint tn (Var nv) = {} ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {cv})) (tn with t_var := tn.t_var |+ (cv,{}))
    (OK (update_var cv w s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ASSIGN [Var nv] [cv]) s = OK (update_var cv w s)` by
    (simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs, mk_inst_def, venomExecSemanticsTheory.exec_pure1_def, eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id ASSIGN [Var nv] [cv]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
          mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, venomExecSemanticsTheory.step_inst_non_invoke] >>
     gvs[update_var_def] >> metis_tac[]) >>
  `step_prov PG G (mk_inst id ASSIGN [Var nv] [cv]) (update_var cv w s) =
      DRESTRICT G (COMPL {cv}) /\
   step_taint (mk_inst id ASSIGN [Var nv] [cv]) s (update_var cv w s) tn =
      tn with t_var := tn.t_var |+ (cv,{})` by
    (irule storage_copy_counter_assign_ghost >> simp[update_var_def]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {cv})) (tn with t_var := tn.t_var |+ (cv,{}))
    (OK (update_var cv w s with vs_inst_idx := SUC s.vs_inst_idx))` by
    (drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
     gvs[mk_inst_def, is_terminator_def] >> metis_tac[]) >>
  drule (cj 2 gas_path_ptr_rules) >> simp[] >> disch_then irule >>
  irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]
QED

Theorem storage_copy_arith_path_ptr:
  (opc = ADD /\ f = word_add \/ opc = MUL /\ f = word_mul) /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc [left;right] [out]) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id opc [left;right] [out]) (update_var out (f a b) s))
    (tn with t_var := tn.t_var |+ (out,{}))
    (OK (update_var out (f a b) s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id opc [left;right] [out]) s = OK (update_var out (f a b) s)` by
    (gvs[] >> simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs, mk_inst_def, venomExecSemanticsTheory.exec_pure2_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc [left;right] [out]) s` by
    (gvs[] >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
          mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, venomExecSemanticsTheory.step_inst_non_invoke] >>
     gvs[update_var_def] >> metis_tac[]) >>
  `new_site_bytes s (update_var out (f a b) s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  `step_taint (mk_inst id opc [left;right] [out]) s (update_var out (f a b) s) tn =
      tn with t_var := tn.t_var |+ (out,{})` by
    (gvs[] >>
     simp[step_taint_def, set_var_taint_def, mk_inst_def, out_taint_def,
          mem_taint_def, step_writes_def, source_memory_write_ranges_def,
          written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
          range_bytes_def, taint_component_equality, DRESTRICT_UNIV]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id opc [left;right] [out]) (update_var out (f a b) s))
    (tn with t_var := tn.t_var |+ (out,{}))
    (OK (update_var out (f a b) s with vs_inst_idx := SUC s.vs_inst_idx))` by
    (drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
     gvs[mk_inst_def, is_terminator_def] >> metis_tac[]) >>
  drule (cj 2 gas_path_ptr_rules) >> simp[] >> disch_then irule >>
  irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]
QED

Theorem storage_copy_add_covers:
  lookup_var root s = SOME a /\ ptr_covers G tn root s capacity /\
  w2n d + needed <= capacity /\ w2n a + w2n d < dimword(:256) ==>
  ptr_covers
    (step_prov PG G (mk_inst id ADD [Var root;offset] [out])
      (update_var out (a+d) s))
    (tn with t_var := tn.t_var |+ (out,{})) out
    (update_var out (a+d) s with vs_inst_idx := SUC s.vs_inst_idx) needed
Proof
  strip_tac >> gvs[bodyPtrDefsTheory.ptr_covers_def] >>
  simp[bodyPtrDefsTheory.ptr_covers_def, step_prov_def, set_prov_def,
       out_prov_def, first_prov_def, op_prov_def, op_taint_def, mk_inst_def,
       FLOOKUP_UPDATE, update_var_def, lookup_var_def, w2n_add_2] >> decide_tac
QED
