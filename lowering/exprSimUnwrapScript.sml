(*
 * unwrap_value's step of the expression simulation (#636)
 *
 * lower_value is compile_expr followed by unwrap_value, which turns the
 * value_vv compile_expr hands out into an operand: none for a StackValue
 * or an aggregate in memory, a load for a word behind a pointer, a copy
 * into a buffer for an aggregate elsewhere.  expr_sim_of_vv_sim sequences
 * compile_expr's counted outcome, which ends in vv_post (expr_vv_sim),
 * with unwrap_value's code, which reads no GAS: unwrap_value_path gives
 * its zero-count gas_path from vv_post to expr_post, and
 * unwrap_value_marked_read binds it to the source's read_result.
 *
 * TOP-LEVEL:
 *   expr_sim_of_vv_sim — expr_vv_sim gives expr_sim
 *   unwrap_value_path  — unwrap_value's zero-GAS path, one lemma per form:
 *                        unwrap_storage_word_path,
 *                        unwrap_runtime_immutable_word_path,
 *                        unwrap_ctor_immutable_word_path,
 *                        unwrap_storage_copy_path,
 *                        unwrap_runtime_code_copy_path,
 *                        unwrap_ctor_code_copy_path
 *   unwrap_value_marked_read — the same, as a marked source execution
 *   expr_sim_of_vv_sim_buffer — the same for an expression lowered to a
 *                        pointer into memory, without the cheated cases
 *   unwrap_value_sim   — unwrap_value's code takes vv_post to expr_post,
 *                        one lemma per form of value_vv:
 *                        expr_post_of_vv_post_stack,
 *                        unwrap_memory_sim (expr_post_of_vv_post_memory,
 *                        and unwrap_memory_word_sim's MLOAD),
 *                        unwrap_runtime_immutable_word_sim (DLOAD),
 *                        unwrap_storage_word_sim (SLOAD/TLOAD),
 *                        unwrap_ctor_immutable_word_sim (ADD of the
 *                        zero base, then ILOAD),
 *                        unwrap_copy_sim (exprSimCopy's copies),
 *                        vv_post_calldata (no calldata pointers)
 *   compile_imm_load_word_ctor_frag — the constructor's immutable word load
 *   vv_post_failed_read — vv_post holds of a result only where it reads
 *
 * Helpers: compile_expr_extends (exprLoweringProps' compile_expr_grows),
 *   compile_ensure_in_memory_extends, unwrap_value_extends,
 *   expr_post_of_vv_post_load, step_DLOAD, immutable_holds_dload,
 *   immutable_holds_iload, compile_imm_load_word_appends,
 *   word_type_slot_size, storage_word_load, storage_holds_load
 *
 * The legacy frag_exec copy lemmas stay in exprSimCopy; the counted copy
 * paths, including the constructor's, are here.
 *)

Theory exprSimUnwrap
Ancestors
  exprSimProps exprSimUnwrapProps
  exprSimDefs
  loweringPosts
  list finite_map
   exprLowering compileEnv loweringStateRelDefs immutableEncoding vyperAST vyperInterpreter
  vyperState
  loweringSlice fragExec freshWrites venomInst venomExecSemantics venomState
  exprSimCopy exprOperandVar vyperEvalExprPreservesScopesDom
  valueEncoding valueEncodingDefs valueEncodingProofs vyperTypeValues vyperStorage vyperValue
  vyperLookupStorage valueCopyBytes
  exprSimMemorySource exprSimMemoryRead gasOutcome gasSummary
  gasSummaryCompose gasExemptCert fragGasMode fragGasPath emitHelperProps
  exprLoweringProps emitHelper exprSimAlloc fragGasSeq exprSimStorageCopy
  storageCopyGasPath
Libs
  pairLib

Theorem runtime_code_copy_post_inst_idx[local,simp]:
  expr_post ctx func ce cx e es sa sb s0 es' v op (s with vs_inst_idx := n) <=>
  expr_post ctx func ce cx e es sa sb s0 es' v op s
Proof
  `!op. eval_operand op (s with vs_inst_idx := n) = eval_operand op s` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  simp[expr_post_def, stmt_state_rel_inst_idx, expr_val_rel_def,
       expr_val_at_def, expr_val_own_def, lookup_var_def, local_region_def]
QED

Theorem runtime_code_copy_seq_path[local]:
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ code /\
  fn_has_code sa sb func /\
  EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; DLOAD; MSTORE]) code /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq code s = OK z ==>
  gas_path ctx func s 0 (OK (z with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  z.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    (fs[EVERY_MEM] >> qx_gen_tac `i` >> disch_tac >>
     qpat_x_assum `!i. MEM i code ==> _` (qspec_then `i` mp_tac) >>
     (impl_tac >- simp[]) >> disch_then strip_assume_tac >>
     simp[is_terminator_def]) >>
  `FILTER (\i. i.inst_opcode = GAS) code = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> qx_gen_tac `i` >> disch_tac >>
     fs[EVERY_MEM] >>
     qpat_x_assum `!i. MEM i code ==> _ \/ _` (qspec_then `i` mp_tac) >>
     (impl_tac >- simp[]) >> disch_then strip_assume_tac >> simp[]) >>
  conj_tac
  >- (`?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
             isPREFIX sb.cs_current_insts bb.bb_instructions` by
        (gvs[fn_has_code_def, same_blocks_def] >> metis_tac[]) >>
      `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
        (qpat_x_assum `isPREFIX _ _` mp_tac >>
         simp[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
         asm_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
         metis_tac[]) >>
      drule_all tuple_run_inst_seq_gas_path >>
      simp[] >> disch_then (qspec_then `ctx` mp_tac) >>
      simp[]) >>
  `z.vs_current_bb = s.vs_current_bb` suffices_by gvs[same_blocks_def] >>
  drule_at (Pos hd)
    (Q.ISPEC `\s:venom_state. s.vs_current_bb` run_inst_seq_preserves_field) >>
  simp[] >> disch_then irule >> rpt strip_tac >>
  fs[EVERY_MEM] >>
  metis_tac[venomInstProofsTheory.step_preserves_control_flow,
            venomExecSemanticsTheory.step_inst_non_invoke]
QED

(* ===== The compile side ===== *)

(* compile_expr only appends to the compile state, and hands out variables
   and instruction ids from its start counters on. *)
Theorem compile_expr_extends:
  !cenv ty e sa vv sm.
    compile_expr cenv ty e sa = (vv, sm) ==>
    cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id
Proof
  rpt gen_tac >> strip_tac >>
  drule (cj 1 exprLoweringPropsTheory.compile_expr_grows) >> simp[]
QED

Theorem compile_imm_load_word_appends:
  !is_ctor imm off.
    cs_appends (context$compile_imm_load_word is_ctor imm off)
Proof
  rpt gen_tac >> Cases_on `imm` >> Cases_on `is_ctor` >>
  simp[contextTheory.compile_imm_load_word_def, cs_appends_emit_helpers] >>
  irule cs_appends_bind >> simp[cs_appends_emit_helpers]
QED

Theorem compile_lit_byte_offset_appends[local]:
  !op off. cs_appends (context$compile_lit_byte_offset op off)
Proof
  rpt gen_tac >> Cases_on `op` >>
  rw[contextTheory.compile_lit_byte_offset_def,
     cs_appends_return, cs_appends_emit_helpers]
QED

Theorem compile_imm_copy_to_memory_appends[local]:
  !n is_ctor imm src dst off.
    cs_appends (context$compile_imm_copy_to_memory is_ctor imm src dst n off)
Proof
  Induct >> rw[contextTheory.compile_imm_copy_to_memory_def,
               cs_appends_return] >>
  rpt (FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind] >>
       rw[compile_lit_byte_offset_appends, compile_imm_load_word_appends,
          cs_appends_emit_helpers]) >>
  simp[]
QED

Theorem compile_ensure_in_memory_appends[local]:
  !pop loc mem_bytes word_count is_ctor imm.
    cs_appends
      (compile_ensure_in_memory pop loc mem_bytes word_count is_ctor imm)
Proof
  rw[contextTheory.compile_ensure_in_memory_def,
     contextTheory.compile_alloc_buffer_def,
     contextTheory.compile_storage_to_memory_def,
     contextTheory.compile_transient_to_memory_def,
     compile_imm_copy_to_memory_appends,
     contextTheory.compile_word_copy_loop_def, contextTheory.compile_word_copy_loop_op_def, contextTheory.compile_word_copy_loop_base_def,
     contextTheory.compile_ptr_load_def, contextTheory.compile_ptr_store_def,
     word_scale_def] >>
  Cases_on `loc` >> rw[] >>
  rpt (FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind,
              IF_CASES_TAC] >>
       rw[cs_appends_prims, cs_appends_return, cs_appends_emit_helpers,
          compile_imm_copy_to_memory_appends]) >>
  rw[cs_appends_prims, cs_appends_return, cs_appends_emit_helpers,
     compile_imm_copy_to_memory_appends]
QED

(* compile_ensure_in_memory's copy only appends to the compile state. *)
Theorem compile_ensure_in_memory_extends:
  !pop loc mem_bytes word_count is_ctor imm sm op sb.
    compile_ensure_in_memory pop loc mem_bytes word_count is_ctor imm sm =
      (op, sb) ==>
    cs_extends sm sb
Proof
  rpt strip_tac >>
  `cs_appends (compile_ensure_in_memory pop loc mem_bytes word_count
                 is_ctor imm)` by simp[compile_ensure_in_memory_appends] >>
  fs[cs_appends_def] >> first_x_assum drule >> simp[]
QED

Theorem emit_op_cs_extends[local]:
  !opc args sm op sb. emit_op opc args sm = (op, sb) ==> cs_extends sm sb
Proof
  rpt strip_tac >>
  `cs_appends (emit_op opc args)` by simp[cs_appends_emit_helpers] >>
  fs[cs_appends_def] >> first_x_assum drule >> simp[]
QED

Theorem unwrap_value_extends:
  !cenv vv sm op sb. unwrap_value cenv vv sm = (op, sb) ==> cs_extends sm sb
Proof
  Cases_on `vv` >>
  rw[unwrap_value_def, comp_return_def, cs_extends_refl]
  >- (rename1 `compile_ptr_load _ _ loc` >> Cases_on `loc` >>
      gvs[contextTheory.compile_ptr_load_def, AllCaseEqs()] >>
      metis_tac[emit_op_cs_extends, cs_appends_def,
                compile_imm_load_word_appends]) >>
  rename1 `p.ptr_location` >> Cases_on `p.ptr_location` >>
  gvs[comp_return_def, cs_extends_refl] >>
  metis_tac[compile_ensure_in_memory_extends]
QED

(* Captured results with the same read have the same compiled-value relation. *)

(* ===== unwrap_value's code ===== *)

(* unwrap_value's code, run where compile_expr's code ends, takes vv_post to
   expr_post.  One lemma per form of value_vv. *)

(* A StackValue: no code. *)
Theorem expr_post_of_vv_post_stack:
  !func cenv cx e es sa sb s0 es' v t op s ctx.
    vv_post ctx func cenv cx e es sa sb s0 es' (Value v) (StackValue t op) s ==>
    expr_post ctx func cenv cx e es sa sb s0 es' v op s
Proof
  rw[vv_post_def, expr_post_def, vv_holds_def, vv_at_def, vv_own_def,
     read_result_def, return_def]
QED

(* An aggregate in memory: the pointer is the operand, no code. *)

(* The end of a one-instruction load of a word: the loaded word in a fresh
   variable, nothing else changed. *)

(* A word in memory: an MLOAD. *)
Theorem unwrap_memory_word_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    emit_op MLOAD [p.ptr_operand] sm = (op, sb) /\
    p.ptr_location = LocMemory /\ is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  rpt strip_tac >> irule frag_exec_pointwise >> rw[] >>
  rename1 `vv_post ctx _ _ _ _ _ _ _ _ _ _ _ s1` >>
  `t = post_value_type cenv e /\
   ?w. eval_operand p.ptr_operand s1 = SOME w /\
       !tvt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME tvt ==>
             mem_word_at (w2n w) s1.vs_memory = typed_val_to_w256 tvt v` by
    (gvs[vv_post_def, vv_holds_def, read_result_def, return_def,
         is_bytestring_word_type] >> metis_tac[]) >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  drule loweringSliceTheory.emit_op_frag >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es'`, `s1`,
                           `mload (w2n w) s1`, `R`] mp_tac) >>
  impl_tac
  >- (rpt conj_tac >- first_assum ACCEPT_TAC >- simp[]
      >- simp[is_terminator_def] >>
      rpt strip_tac >> irule emitHelperPropsTheory.step_MLOAD >>
      first_assum ACCEPT_TAC) >>
  strip_tac >> irule frag_exec_conseq >> first_x_assum (irule_at Any) >>
  simp[] >> rpt strip_tac
  >~ [`expr_post`] >- (
  irule expr_post_of_vv_post_load_physical >>
  qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload, SF SFY_ss]) >>
  gvs[vv_post_def]
QED

Theorem step_DLOAD:
  !op1 v1 id out ss.
    eval_operand op1 ss = SOME v1 ==>
    step_inst_base (mk_inst id DLOAD [op1] [out]) ss =
      OK (update_var out
            (word_of_bytes T (0w:bytes32)
               (TAKE 32 (DROP (w2n v1) ss.vs_data_section ++
                         REPLICATE 32 0w))) ss)
Proof
  rpt strip_tac >>
  simp[Once venomExecSemanticsTheory.step_inst_base_def, mk_inst_def] >>
  simp[venomExecSemanticsTheory.exec_read1_def]
QED

(* Admissibility rules out type/value mismatches; a word type's memory
   representation is its typed word encoding, including zero padding. *)
Theorem immutable_word_mem_word_at[local]:
  !tenv t tv v off mem.
    evaluate_type tenv t = SOME tv /\ is_word_type t /\
    immutable_value_admissible tv v /\ val_in_memory tv v off mem ==>
    mem_word_at off mem = typed_val_to_w256 tv v
Proof
  rpt strip_tac >> Cases_on `t`
  >~ [`BaseT bt`]
  >- (Cases_on `bt` >>
      TRY (rename1 `BytesT bd` >> Cases_on `bd`) >>
      gvs[vyperValueTheory.evaluate_type_def, is_word_type_def,
          AllCaseEqs()] >>
      Cases_on `v` >>
      gvs[immutable_value_admissible_def,
          valueEncodingPropsTheory.val_in_memory_fixed_bytes,
          valueEncodingPropsTheory.val_in_memory_address,
          val_in_memory_def, typed_val_to_w256_def]) >>
  gvs[is_word_type_def, vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >>
  gvs[immutable_value_admissible_def, val_in_memory_def,
      typed_val_to_w256_def]
QED

(* At runtime a word immutable is in the data section at its offset, as
   immutables_rel says.  Aggregates instead occupy their full memory layout. *)
Theorem immutable_holds_dload:
  !func cenv cx es s t v w ctx.
    stmt_state_rel ctx func cenv cx es s /\ ~cenv.ce_is_ctor /\
    is_word_type t /\ immutable_holds cenv cx t (Value v) w es s ==>
    ?tvt. evaluate_type (get_tenv cx) t = SOME tvt /\
          word_of_bytes T (0w:bytes32)
            (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w)) =
          typed_val_to_w256 tvt v
Proof
  rw[immutable_holds_def, exprLoweringPropsTheory.stmt_state_rel_def,
     state_rel_def, immutables_rel_def, read_result_def, return_def] >>
  gvs[] >> first_x_assum drule_all >> strip_tac >>
  gvs[sub_layout_def] >> first_x_assum drule >> strip_tac >>
  `off + k < dimword (:256)` by DECIDE_TAC >>
  `mem_word_at (off + k) s.vs_data_section = typed_val_to_w256 tvt v` by
    (irule val_in_memory_word_type >> metis_tac[]) >>
  gvs[valueEncodingDefsTheory.mem_word_at_def]
QED

(* A word immutable at runtime: a DLOAD. *)
Theorem unwrap_runtime_immutable_word_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    emit_op DLOAD [p.ptr_operand] sm = (op, sb) /\
    p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  rpt strip_tac >> irule frag_exec_pointwise >> rw[] >>
  rename1 `vv_post ctx _ _ _ _ _ _ _ _ _ _ _ s1` >>
  `t = post_value_type cenv e /\
   ?w. eval_operand p.ptr_operand s1 = SOME w /\
       immutable_holds cenv cx (post_value_type cenv e) (Value v) w es' s1 /\
       stmt_state_rel ctx func cenv cx es' s1` by
    gvs[vv_post_def, vv_holds_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  drule_all immutable_holds_dload >> strip_tac >>
  drule loweringSliceTheory.emit_op_frag >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es'`, `s1`,
    `word_of_bytes T (0w:bytes32)
       (TAKE 32 (DROP (w2n w) s1.vs_data_section ++ REPLICATE 32 0w))`,
    `R`] mp_tac) >>
  impl_tac
  >- (rpt conj_tac >- first_assum ACCEPT_TAC >- simp[]
      >- simp[is_terminator_def] >>
      rpt strip_tac >> irule step_DLOAD >> first_assum ACCEPT_TAC) >>
  strip_tac >> irule frag_exec_conseq >> first_x_assum (irule_at Any) >>
  simp[] >> rpt strip_tac
  >~ [`expr_post`] >- (
  irule expr_post_of_vv_post_load_physical >>
  qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[SF SFY_ss]) >>
  gvs[]
QED

(* A pointer into memory: an MLOAD for a word, the pointer itself for an
   aggregate. *)
Theorem unwrap_memory_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocMemory /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  rpt strip_tac >> Cases_on `is_word_type t`
  >- (irule unwrap_memory_word_sim >>
      gvs[unwrap_value_def, contextTheory.compile_ptr_load_def]) >>
  gvs[unwrap_value_def, comp_return_def] >> irule frag_exec_refl >>
  rw[] >> metis_tac[expr_post_of_vv_post_memory]
QED

(* A word type takes one slot. *)
Theorem word_type_slot_size:
  !tenv t tv.
    is_word_type t /\ evaluate_type tenv t = SOME tv ==> type_slot_size tv = 1
Proof
  rpt strip_tac >>
  `(?n. t = BaseT (UintT n)) \/ (?n. t = BaseT (IntT n)) \/
   t = BaseT BoolT \/ t = BaseT AddressT \/ t = BaseT DecimalT \/
   (?m. t = BaseT (BytesT (Fixed m)) /\ m <= 32) \/ (?n. t = FlagT n)` by
    (Cases_on `t` >> fs[is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> fs[is_word_type_def]) >>
  gvs[evaluate_type_def, AllCaseEqs(), vyperValueTheory.type_slot_size_def]
QED

(* A word's slot holds its value's encoding: the slot is canonical
   (slots_in_range), so it encodes back to what it decodes to. *)
Theorem storage_word_load[local]:
  !cx t tvt storage w v.
    is_word_type t /\ evaluate_type (get_tenv cx) t = SOME tvt /\
    decode_value storage (w2n w) tvt = SOME v /\
    slots_in_range storage (w2n w) tvt ==>
    lookup_storage w storage = typed_val_to_w256 tvt v
Proof
  rpt strip_tac >>
  drule vyperTypeValuesTheory.evaluate_type_well_formed_type_value >>
  strip_tac >>
  Cases_on `t` >> gvs[is_word_type_def] >>
  TRY (rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_word_type_def]) >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd`) >>
  gvs[is_word_type_def, evaluate_type_def, AllCaseEqs()] >>
  gvs[decode_value_def, slots_in_range_def, word_slot_canonical_def,
      read_slot_def, decode_base_from_slot_def, encode_base_to_slot_def,
      typed_val_to_w256_def, val_to_w256_def, bool_to_slot_def,
      AllCaseEqs(), valueEncodingProofsTheory.word_of_bytes_be_pad_right]
QED

(* At runtime the word a storage or transient load returns is the value's:
   storage_holds makes the slot agree with the source's. *)
Theorem storage_holds_load:
  !cx es s t v w tr tvt.
    is_word_type t /\ storage_holds cx tr t (Value v) w es s /\
    evaluate_type (get_tenv cx) t = SOME tvt ==>
    (if tr then tload w s else sload w s) = typed_val_to_w256 tvt v
Proof
  rpt gen_tac >> strip_tac >>
  gvs[storage_holds_def, read_result_def, return_def] >>
  gvs[read_storage_slot_def, vyperStorageBackendTheory.get_storage_backend_eq,
      bind_def, lift_option_def, AllCaseEqs(), return_def, raise_def] >>
  qpat_x_assum `option_CASE _ _ _ _ = _` mp_tac >> CASE_TAC >>
  simp[raise_def, return_def] >> strip_tac >> gvs[] >>
  drule_all storage_word_load >> strip_tac >>
  `0 < type_slot_size tvt` by (drule_all word_type_slot_size >> simp[]) >>
  drule_all accountsRelPropsTheory.storage_range_agree_head >> strip_tac >>
  Cases_on `tr` >> gvs[sload_def, tload_def]
QED

(* A word in storage or transient storage: an SLOAD or TLOAD. *)
Theorem unwrap_storage_word_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  rpt strip_tac >>
  gvs[unwrap_value_def, contextTheory.compile_ptr_load_def] >> (
  irule frag_exec_pointwise >> rw[] >>
  rename1 `vv_post ctx _ _ _ _ _ _ _ _ _ _ _ s1` >>
  `t = post_value_type cenv e /\
   ?w. eval_operand p.ptr_operand s1 = SOME w /\
       storage_holds cx (p.ptr_location = LocTransient) (post_value_type cenv e)
         (Value v) w es' s1 /\
       stmt_state_rel ctx func cenv cx es' s1` by
    gvs[vv_post_def, vv_holds_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  `!tvt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME tvt ==>
         (if p.ptr_location = LocTransient then tload w s1 else sload w s1) =
         typed_val_to_w256 tvt v` by (
    rpt strip_tac >> drule_all storage_holds_load >> simp[]) >>
  drule loweringSliceTheory.emit_op_frag >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es'`, `s1`,
    `if p.ptr_location = LocTransient then tload w s1 else sload w s1`,
    `R`] mp_tac) >>
  impl_tac
  >- (rpt conj_tac >- first_assum ACCEPT_TAC >- simp[]
      >- simp[is_terminator_def] >>
      rpt strip_tac >> gvs[step_inst_base_def, exec_read1_def]) >>
  strip_tac >> irule frag_exec_conseq >> first_x_assum (irule_at Any) >>
  simp[] >> rpt strip_tac
  >~ [`expr_post`] >- (
  irule expr_post_of_vv_post_load_physical >>
  qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  gvs[SF SFY_ss]) >>
  gvs[])
QED

(* In the constructor a word immutable is staged in memory at its offset, as
   immutables_rel says. *)
Theorem immutable_holds_iload:
  !func cenv cx es s t v w ctx.
    stmt_state_rel ctx func cenv cx es s /\ cenv.ce_is_ctor /\
    is_word_type t /\ immutable_holds cenv cx t (Value v) w es s ==>
    ?tvt. evaluate_type (get_tenv cx) t = SOME tvt /\
          mload (w2n w) s = typed_val_to_w256 tvt v
Proof
  rw[immutable_holds_def, exprLoweringPropsTheory.stmt_state_rel_def,
     state_rel_def, immutables_rel_def, read_result_def, return_def] >>
  `val_in_memory tvt v (off + k) s.vs_memory` by
    (gvs[] >> first_x_assum drule_all >> strip_tac >>
     gvs[sub_layout_def] >> first_x_assum drule >> simp[]) >>
  `off + k < dimword (:256)` by (fs[sub_layout_def] >> DECIDE_TAC) >>
  `mem_word_at (off + k) s.vs_memory = typed_val_to_w256 tvt v` by
    (irule val_in_memory_word_type >> metis_tac[]) >>
  gvs[valueEncodingDefsTheory.mem_word_at_def, mload_def]
QED

(* The ILOAD of a constructor immutable word reads memory. *)
Theorem step_ILOAD[local]:
  !id a out s w.
    eval_operand a s = SOME w ==>
    step_inst_base (mk_inst id ILOAD [a] [out]) s =
    OK (update_var out (mload (w2n w) s) s)
Proof
  simp[step_inst_base_def, exec_read1_def, mk_inst_def]
QED

(* The base of a constructor immutable access holds 0, so ADD of it is the
   offset. *)
Theorem step_ADD_imm_base[local]:
  !ctx func cenv cx es id pop ib out s w.
    stmt_state_rel ctx func cenv cx es s /\
    cenv.ce_imm_alloca = SOME ib /\ eval_operand pop s = SOME w ==>
    step_inst_base (mk_inst id ADD [pop; ib] [out]) s =
    OK (update_var out w s)
Proof
  rpt strip_tac >>
  `eval_operand ib s = SOME 0w` by
    gvs[exprLoweringPropsTheory.stmt_state_rel_def, immutable_base_zero_def] >>
  simp[step_inst_base_def, exec_pure2_def, mk_inst_def, wordsTheory.WORD_ADD_0]
QED

(* A constructor immutable word load at offset pop: ADD of the base, then
   ILOAD, or ILOAD alone without a base.  It reads the memory word at pop. *)
Theorem compile_imm_load_word_ctor_frag:
  !ctx func cenv cx es pop sm op sb s0 w R.
    compile_imm_load_word T cenv.ce_imm_alloca pop sm = (op, sb) /\
    local_ptrs_reserved cenv sm /\ eval_operand pop s0 = SOME w ==>
    frag_exec ctx sm sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. stmt_state_rel ctx func cenv cx es s /\
           eval_operand op s = SOME (mload (w2n w) s0) /\
           (!x w'. not_fresh_at sm x /\ lookup_var x s0 = SOME w' ==>
                   lookup_var x s = SOME w') /\
           (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                    FLOOKUP s.vs_allocas aid = SOME b) /\
           s.vs_memory = s0.vs_memory) R
Proof
  rpt strip_tac >> Cases_on `cenv.ce_imm_alloca` >>
  gvs[contextTheory.compile_imm_load_word_def]
  >- (irule loweringSliceTheory.emit_op_frag >> simp[] >>
      qexistsl [`[pop]`, `ILOAD`] >> simp[is_terminator_def] >>
      rpt strip_tac >> irule step_ILOAD >> simp[]) >>
  rename1 `cenv.ce_imm_alloca = SOME ib` >>
  qpat_x_assum `comp_bind _ _ _ = _` mp_tac >>
  simp[comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_op ADD [pop; ib] sm = (addr, sm1)` >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  qpat_assum `emit_op ADD _ _ = _`
    (strip_assume_tac o MATCH_MP emitHelperPropsTheory.emitted_insts_emit_op) >>
  `local_ptrs_reserved cenv sm1` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `ADD`, `[pop; ib]`, `sm`,
               `addr`, `sm1`, `s0`, `w`, `R`] mp_tac
    loweringSliceTheory.emit_op_frag >>
  impl_tac
  >- (simp[is_terminator_def] >> rpt strip_tac >>
      irule step_ADD_imm_base >> metis_tac[]) >>
  disch_then (fn th => irule (MATCH_MP frag_exec_then th)) >>
  rpt conj_tac
  >~ [`cs_extends sm sm1`] >- metis_tac[emit_op_cs_extends]
  >~ [`cs_extends sm1 sb`] >- metis_tac[emit_op_cs_extends] >>
  qx_gen_tac `t` >> BETA_TAC >> strip_tac >>
  qpat_x_assum `emit_op ILOAD _ _ = _` assume_tac >>
  drule loweringSliceTheory.emit_op_frag >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `t`,
    `mload (w2n w) t`, `R`] mp_tac) >>
  impl_tac
  >- (simp[is_terminator_def] >> rpt strip_tac >>
      irule step_ILOAD >> gvs[]) >>
  strip_tac >> irule frag_exec_conseq >> first_x_assum (irule_at Any) >>
  simp[] >> rpt strip_tac >> gvs[mload_def] >>
  first_x_assum irule >> conj_tac
  >- (first_x_assum irule >> simp[]) >>
  fs[not_fresh_at_def]
QED

(* A word immutable in the constructor: a load from the staged immutables,
   relative to the base, which holds 0. *)
Theorem unwrap_ctor_immutable_word_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ cenv.ce_is_ctor /\ is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  rpt strip_tac >> irule frag_exec_pointwise >> rw[] >>
  rename1 `vv_post ctx _ _ _ _ _ _ _ _ _ _ _ s1` >>
  `t = post_value_type cenv e /\
   ?w. eval_operand p.ptr_operand s1 = SOME w /\
       immutable_holds cenv cx (post_value_type cenv e) (Value v) w es' s1 /\
       stmt_state_rel ctx func cenv cx es' s1` by
    gvs[vv_post_def, vv_holds_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  drule_all immutable_holds_iload >> strip_tac >>
  `compile_imm_load_word T cenv.ce_imm_alloca p.ptr_operand sm = (op, sb)` by
    gvs[unwrap_value_def, contextTheory.compile_ptr_load_def] >>
  drule_all compile_imm_load_word_ctor_frag >>
  disch_then (qspecl_then [`ctx`, `func`, `cx`, `es'`, `R`] assume_tac) >>
  irule frag_exec_conseq >> first_x_assum (irule_at Any) >>
  simp[] >> rpt strip_tac
  >~ [`expr_post`] >- (
  qspecl_then [`func`, `cenv`, `cx`, `e`, `es`, `sa`, `sm`, `sb`, `s0`, `es'`,
               `v`, `post_value_type cenv e`, `p`, `op`, `s1`, `s`,
               `mload (w2n w) s1`, `ctx`]
    mp_tac expr_post_of_vv_post_load_physical >>
  impl_tac >- (asm_rewrite_tac[] >> rpt strip_tac >> gvs[]) >>
  simp[]) >>
  gvs[]
QED
(* An aggregate in storage, transient storage or code: a copy into a buffer
   of the expression's own, allocated at instruction id sm.cs_next_id
   (exprSimCopy).  The buffer is type_memory_bytes of the value_vv's type,
   which vv_post makes the expression's; the last premise says that is the
   value's memory size and fits Python's allocation limit. *)
Theorem unwrap_copy_physical_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
     p.ptr_location = LocCode) /\ ~is_word_type t /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME tvt /\
           ~is_word_type (post_value_type cenv e) ==>
           type_memory_bytes cenv (post_value_type cenv e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  rpt strip_tac >>
  (reverse (Cases_on `t = post_value_type cenv e`)
   >- (irule frag_exec_conseq >> qexistsl_tac [`\s. F`, `\s. F`, `R`] >>
       gvs[fragExecTheory.frag_exec_false_pre, vv_post_def, vv_holds_def])) >>
  gvs[]
  >~ [`p.ptr_location = LocCode`]
  >- (Cases_on `cenv.ce_is_ctor`
      >- (irule exprSimCopyTheory.unwrap_ctor_code_copy_sim >> gvs[]) >>
      irule exprSimCopyTheory.unwrap_runtime_code_copy_sim >> gvs[]) >>
  irule exprSimCopyTheory.unwrap_storage_copy_sim >> gvs[]
QED

Theorem unwrap_copy_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
     p.ptr_location = LocCode) /\ ~is_word_type t /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
           ~is_word_type (expr_type e) ==>
           type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  rpt strip_tac >> irule unwrap_copy_physical_sim >> simp[]
QED

(* No value_vv points into calldata. *)
Theorem vv_post_calldata:
  !func cenv cx e es sa sm s0 es' tv t p s ctx.
    p.ptr_location = LocCalldata ==>
    ~vv_post ctx func cenv cx e es sa sm s0 es' tv (LocatedValue t p) s
Proof
  rw[vv_post_def, vv_holds_def]
QED

Theorem unwrap_value_physical_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v vv op R.
    unwrap_value cenv vv sm = (op, sb) /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME tvt /\
           ~is_word_type (post_value_type cenv e) ==>
           type_memory_bytes cenv (post_value_type cenv e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v) vv s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  rpt strip_tac >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  Cases_on `vv`
  >- (gvs[unwrap_value_def, comp_return_def] >> irule frag_exec_refl >>
      rw[] >> metis_tac[expr_post_of_vv_post_stack]) >>
  rename1 `LocatedValue t p` >>
  RULE_ASSUM_TAC (REWRITE_RULE [contextTheory.vv_operand_def]) >>
  Cases_on `p.ptr_location = LocCalldata`
  >- (irule frag_exec_conseq >>
      qexistsl_tac [`\s. F`, `\s. F`, `R`] >>
      gvs[fragExecTheory.frag_exec_false_pre, vv_post_calldata]) >>
  Cases_on `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient`
  >- (Cases_on `is_word_type t`
      >- (irule unwrap_storage_word_sim >> gvs[]) >>
      irule unwrap_copy_physical_sim >> gvs[] >>
      qpat_x_assum `_ \/ _` strip_assume_tac >> simp[]) >>
  Cases_on `p.ptr_location = LocCode`
  >- (reverse (Cases_on `is_word_type t`)
      >- (irule unwrap_copy_physical_sim >> gvs[]) >>
      Cases_on `cenv.ce_is_ctor`
      >- (irule unwrap_ctor_immutable_word_sim >> gvs[]) >>
      irule unwrap_runtime_immutable_word_sim >>
      gvs[unwrap_value_def, contextTheory.compile_ptr_load_def,
          contextTheory.compile_imm_load_word_def]) >>
  `p.ptr_location = LocMemory` by (Cases_on `p.ptr_location` >> gvs[]) >>
  irule unwrap_memory_sim >> simp[]
QED

Theorem unwrap_value_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v vv op R.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv vv sm = (op, sb) /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
           ~is_word_type (expr_type e) ==>
           type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v) vv s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  rpt strip_tac >> irule unwrap_value_physical_sim >> simp[]
QED

(* vv_post holds of a result only where it reads. *)
Theorem vv_post_failed_read:
  !func cenv cx e es sa sm s0 es' raw vv s exc ctx.
    read_result cx raw es' = (INR exc, es') ==>
    ~vv_post ctx func cenv cx e es sa sm s0 es' raw vv s
Proof
  rpt strip_tac >> Cases_on `vv` >>
  gvs[vv_post_def, vv_holds_def, storage_holds_def, immutable_holds_def] >>
  rename1 `eval_operand place_ptr.ptr_operand s = SOME word` >>
  Cases_on `place_ptr.ptr_location` >> gvs[]
QED

Theorem unwrap_memory_read_result_sim:
  !ctx func cenv cx e es sa sm sb s0 es' raw res t p op.
    read_result cx raw es' = (res, es') /\
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocMemory /\ local_ptrs_reserved cenv sm /\
    sa.cs_next_var <= sm.cs_next_var ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' raw (LocatedValue t p) s)
      (\s. ?v. res = INL v /\ expr_post ctx func cenv cx e es sa sb s0 es' v op s)
      (expr_exit res)
Proof
  rpt strip_tac >> Cases_on `res`
  >- (rename1 `read_result cx raw es' = (INL v, es')` >>
      drule vv_post_read_result >> strip_tac >>
      irule frag_exec_conseq >>
      qexistsl_tac
        [`\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s`,
         `\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s`,
         `\r. F`] >>
      simp[] >> irule unwrap_memory_sim >> simp[]) >>
  rename1 `read_result cx raw es' = (INR exc, es')` >>
  irule frag_exec_conseq >> qexistsl_tac [`\s. F`, `\s. F`, `\r. F`] >>
  simp[fragExecTheory.frag_exec_false_pre] >> metis_tac[vv_post_failed_read]
QED

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag unwrap_memory_read_result_sim)
  in
    if null axioms andalso null (Thm.hyp unwrap_memory_read_result_sim) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then
      print "MEMORY_FORCE_AUDIT unwrap_memory_read_result_sim OK\n"
    else raise Fail "unwrap_memory_read_result_sim: admitted proof dependency"
  end;


(* ===== Counted unwrap_value suffixes =====

   The counted judgments need the actual target path of unwrap_value's code:
   each lemma below runs that code from vv_post to expr_post along a GAS-free
   path (it reads no gas), mirroring the frag_exec lemmas above. *)

(* One emitted non-GAS instruction writing w to a fresh variable. *)
Theorem emit_op_path[local]:
  !ctx func cenv cx es opc args sa op sb s0 w.
    emit_op opc args sa = (op, sb) /\ local_ptrs_reserved cenv sa /\
    fn_has_code sa sb func /\
    opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!out. step_inst_base (mk_inst sa.cs_next_id opc args [out]) s0 =
           OK (update_var out w s0)) ==>
    ?s. gas_path ctx func s0 0 (OK s) /\
        s.vs_current_bb = sb.cs_current_bb /\
        s.vs_inst_idx = LENGTH sb.cs_current_insts /\
        stmt_state_rel ctx func cenv cx es s /\ eval_operand op s = SOME w /\
        (!x w'. not_fresh_at sa x /\ lookup_var x s0 = SOME w' ==>
                lookup_var x s = SOME w') /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                 FLOOKUP s.vs_allocas aid = SOME b) /\
        s.vs_memory = s0.vs_memory
Proof
  rpt strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  qexists_tac `update_var out w s0 with vs_inst_idx := SUC s0.vs_inst_idx` >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `not_local_ptr cenv es.scopes out` by
    (qunabbrev_tac `out` >> irule local_ptrs_reserved_fresh >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `op = Var out /\ sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    gvs[Abbr `out`, emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  rpt conj_tac
  >- (qunabbrev_tac `out` >> irule emitHelperPropsTheory.emit_op_zero_path >>
      simp[] >> metis_tac[])
  >- simp[update_var_def]
  >- simp[update_var_def]
  >- (simp[stmt_state_rel_inst_idx] >> irule stmt_state_rel_update_var >>
      simp[])
  >- simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
  >- (rpt strip_tac >> res_tac >>
      gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE])
  >- simp[update_var_def] >>
  simp[update_var_def]
QED

Theorem unwrap_storage_word_path:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op s.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    is_word_type t /\ local_ptrs_reserved cenv sm /\
    sa.cs_next_var <= sm.cs_next_var /\ fn_has_code sm sb func /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >> (
  `t = post_value_type cenv e /\
   ?w. eval_operand p.ptr_operand s = SOME w /\
       storage_holds cx (p.ptr_location = LocTransient) (post_value_type cenv e)
         (Value v) w es' s /\
       stmt_state_rel ctx func cenv cx es' s` by
    gvs[vv_post_def, vv_holds_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  qabbrev_tac `ld = if p.ptr_location = LocTransient then tload w s
                    else sload w s` >>
  `!tvt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME tvt ==>
         ld = typed_val_to_w256 tvt v` by
    (rpt strip_tac >> qunabbrev_tac `ld` >>
     drule_all storage_holds_load >> simp[]) >>
  `emit_op (if p.ptr_location = LocTransient then TLOAD else SLOAD)
     [p.ptr_operand] sm = (op, sb)` by
    gvs[unwrap_value_def, contextTheory.compile_ptr_load_def] >>
  drule emit_op_path >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es'`, `s`, `ld`]
    mp_tac) >>
  impl_tac
  >- (rw[is_terminator_def, Abbr `ld`] >>
      gvs[step_inst_base_def, exec_read1_def, mk_inst_def]) >>
  strip_tac >> rename1 `gas_path _ _ s 0 (OK u)` >>
  qexists_tac `u` >> simp[] >>
  irule expr_post_of_vv_post_load_physical >> simp[] >>
  qexistsl_tac [`p`, `s`, `sm`, `post_value_type cenv e`] >> simp[])
QED

Theorem unwrap_runtime_immutable_word_path:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op s.
    emit_op DLOAD [p.ptr_operand] sm = (op, sb) /\
    p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    fn_has_code sm sb func /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  `t = post_value_type cenv e /\
   ?w. eval_operand p.ptr_operand s = SOME w /\
       immutable_holds cenv cx (post_value_type cenv e) (Value v) w es' s /\
       stmt_state_rel ctx func cenv cx es' s` by
    gvs[vv_post_def, vv_holds_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  drule_all immutable_holds_dload >> strip_tac >>
  drule emit_op_path >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es'`, `s`,
    `typed_val_to_w256 tvt v`] mp_tac) >>
  impl_tac
  >- (simp[is_terminator_def] >> gen_tac >>
      qpat_x_assum `word_of_bytes _ _ _ = _` (SUBST1_TAC o SYM) >>
      irule step_DLOAD >> first_assum ACCEPT_TAC) >>
  strip_tac >> rename1 `gas_path _ _ s 0 (OK u)` >>
  qexists_tac `u` >> simp[] >>
  irule expr_post_of_vv_post_load_physical >> simp[] >>
  qexistsl_tac [`p`, `s`, `sm`, `post_value_type cenv e`] >> simp[]
QED

(* compile_imm_load_word_ctor_frag's counted form. *)
Theorem compile_imm_load_word_ctor_path:
  !ctx func cenv cx es pop sm op sb s0 w.
    compile_imm_load_word T cenv.ce_imm_alloca pop sm = (op, sb) /\
    local_ptrs_reserved cenv sm /\ fn_has_code sm sb func /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sm.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sm.cs_current_insts /\
    eval_operand pop s0 = SOME w ==>
    ?s. gas_path ctx func s0 0 (OK s) /\
        s.vs_current_bb = sb.cs_current_bb /\
        s.vs_inst_idx = LENGTH sb.cs_current_insts /\
        stmt_state_rel ctx func cenv cx es s /\
        eval_operand op s = SOME (mload (w2n w) s0) /\
        (!x w'. not_fresh_at sm x /\ lookup_var x s0 = SOME w' ==>
                lookup_var x s = SOME w') /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                 FLOOKUP s.vs_allocas aid = SOME b) /\
        s.vs_memory = s0.vs_memory
Proof
  rpt strip_tac >> Cases_on `cenv.ce_imm_alloca` >>
  gvs[contextTheory.compile_imm_load_word_def]
  >- (drule emit_op_path >>
      disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `s0`,
        `mload (w2n w) s0`] mp_tac) >>
      impl_tac
      >- (simp[is_terminator_def] >> rpt strip_tac >> irule step_ILOAD >>
          simp[]) >>
      strip_tac >> goal_assum drule >> simp[]) >>
  rename1 `cenv.ce_imm_alloca = SOME ib` >>
  qpat_x_assum `comp_bind _ _ _ = _` mp_tac >>
  simp[comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_op ADD [pop; ib] sm = (addr, sm1)` >>
  `cs_extends sm sm1 /\ cs_extends sm1 sb` by metis_tac[emit_op_cs_extends] >>
  `fn_has_code sm sm1 func /\ fn_has_code sm1 sb func` by
    metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved cenv sm1` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sm` >>
     gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
         comp_ignore_bind_def, comp_return_def, emit_def]) >>
  qpat_x_assum `emit_op ADD _ _ = _` assume_tac >>
  drule emit_op_path >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `s0`, `w`]
    mp_tac) >>
  impl_tac
  >- (simp[is_terminator_def] >> rpt strip_tac >>
      irule step_ADD_imm_base >> metis_tac[]) >>
  strip_tac >> rename1 `gas_path _ _ s0 0 (OK s1)` >>
  `~s1.vs_halted` by metis_tac[gas_path_normal] >>
  qpat_x_assum `emit_op ILOAD _ _ = _` assume_tac >>
  drule emit_op_path >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `s1`,
    `mload (w2n w) s1`] mp_tac) >>
  impl_tac
  >- (simp[is_terminator_def] >> rpt strip_tac >> irule step_ILOAD >>
      simp[]) >>
  strip_tac >> rename1 `gas_path _ _ s1 0 (OK s2)` >>
  qexists_tac `s2` >> gvs[mload_def] >>
  conj_tac
  >- (`0 = 0 + 0` by simp[] >> pop_assum SUBST1_TAC >>
      irule gas_path_then >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum irule >> conj_tac
  >- (first_x_assum irule >> simp[]) >>
  gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
      comp_ignore_bind_def, comp_return_def, emit_def, not_fresh_at_def]
QED

Theorem unwrap_ctor_immutable_word_path:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op s.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ cenv.ce_is_ctor /\ is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    fn_has_code sm sb func /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  `t = post_value_type cenv e /\
   ?w. eval_operand p.ptr_operand s = SOME w /\
       immutable_holds cenv cx (post_value_type cenv e) (Value v) w es' s /\
       stmt_state_rel ctx func cenv cx es' s` by
    gvs[vv_post_def, vv_holds_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  drule_all immutable_holds_iload >> strip_tac >>
  `compile_imm_load_word T cenv.ce_imm_alloca p.ptr_operand sm = (op, sb)` by
    gvs[unwrap_value_def, contextTheory.compile_ptr_load_def] >>
  drule compile_imm_load_word_ctor_path >>
  disch_then (qspecl_then [`ctx`, `func`, `cx`, `es'`, `s`, `w`] mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >> rename1 `gas_path _ _ s 0 (OK u)` >>
  qexists_tac `u` >> simp[] >>
  irule expr_post_of_vv_post_load_physical >> simp[] >>
  qexistsl_tac [`p`, `s`, `sm`, `post_value_type cenv e`] >> simp[]
QED

Theorem alloc_buffer_run_path[local]:
  compile_alloc_buffer sz sm = (buf,mid) /\ fn_has_code sm mid func /\
  run_inst_seq (emitted_insts sm mid) s = OK t /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  gas_path ctx func s 0
    (OK (t with vs_inst_idx := LENGTH mid.cs_current_insts)) /\
  ~t.vs_halted /\ t.vs_current_bb = mid.cs_current_bb
Proof
  strip_tac >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
       comp_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       comp_ignore_bind_def, emit_def] >> strip_tac >> gvs[] >>
  gvs[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  conj_tac
  >- (gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
      drule_at (Pat `run_inst_seq _ _ = OK _`) tuple_run_inst_seq_gas_path >>
      disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
      pure_rewrite_tac[GSYM APPEND_ASSOC] >>
      simp[mk_inst_def, is_terminator_def, rich_listTheory.IS_PREFIX_APPEND,
           DROP_APPEND]) >>
  gvs[run_inst_seq_def, step_inst_base_def, mk_inst_def,
      exec_alloca_def, AllCaseEqs(), update_var_def]
QED

Theorem alloc_buffer_source_path[local]:
  !ctx func cenv cx es sm mid buf sz s src a.
    compile_alloc_buffer sz sm = (buf,mid) /\ fn_has_code sm mid func /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sm /\ sz < dimword (:256) /\
    eval_operand src s = SOME a /\
    (!x. src = Var x ==> not_fresh_at sm x) /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u w. gas_path ctx func s 0 (OK u) /\
      ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
      u.vs_inst_idx = LENGTH mid.cs_current_insts /\
      eval_operand src u = SOME a /\
      stmt_state_rel ctx func cenv cx es u /\
      eval_operand buf.buf_operand u = SOME w /\
      FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,sz) /\
      w2n w + sz < dimword (:256) /\ u.vs_memory = s.vs_memory /\
      u.vs_labels = s.vs_labels /\ sm.cs_next_id < mid.cs_next_id /\
      (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP u.vs_allocas aid = SOME entry) /\
      (!aid b len. aid < sm.cs_next_id /\
         FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
         regions_disjoint (w2n w) sz b len) /\
      (!name b len. local_region cenv es.scopes u name b len ==>
         regions_disjoint (w2n w) sz b len) /\
      (?p. buf.buf_operand = Var p /\ not_fresh_at mid p) /\
      contract_storage u = contract_storage s /\
      contract_transient u = contract_transient s
Proof
  rpt gen_tac >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `t.vs_labels = s.vs_labels` by metis_tac[hash_alloc_buffer_labels] >>
  `contract_storage t = contract_storage s /\
   contract_transient t = contract_transient s` by
    metis_tac[alloc_buffer_storage] >>
  `eval_operand src t = SOME a` by
    (Cases_on `src` >> gvs[eval_operand_def]) >>
  drule_all alloc_buffer_run_path >> strip_tac >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH mid.cs_current_insts`, `w`] >>
  simp[] >> Cases_on `src` >>
  gvs[stmt_state_rel_inst_idx, eval_operand_def, lookup_var_def,
      local_region_def, venomStateTheory.contract_storage_def,
      venomStateTheory.contract_transient_def] >> metis_tac[]
QED

Theorem storage_unwrap_word_run[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
     emit_void MSTORE [dst; v] od sa = (u,sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  b+32 < 2**256 ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    copy_prefix loc a b 1 s 1 t /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_current_bb = s.vs_current_bb
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule storage_copy_word_layout >> strip_tac >>
  qabbrev_tac `v = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `w = copy_runtime_word loc s a` >>
  `step_inst_base (mk_inst sa.cs_next_id
    (if loc = LocStorage then SLOAD else TLOAD) [src] [v]) s =
    OK (update_var v w s)` by
    (gvs[step_inst_base_opcode_eqs, exec_read1_def, mk_inst_def,
         Abbr `w`, copy_runtime_word_def]) >>
  `eval_operand dst (update_var v w s) = SOME (n2w b)` by
    (Cases_on `dst` >> gvs[eval_operand_def, lookup_var_update_var] >> metis_tac[]) >>
  `w2n (n2w b : bytes32) = b` by
    (gvs[wordsTheory.w2n_n2w, wordsTheory.dimword_def] >> decide_tac) >>
  `step_inst_base (mk_inst (sa.cs_next_id+1) MSTORE [dst; Var v] [])
    (update_var v w s) = OK (mstore b w (update_var v w s))` by
    (qpat_assum `w2n (n2w b : bytes32) = b`
       (fn th => once_rewrite_tac[GSYM th]) >>
     irule step_MSTORE >> simp[eval_operand_update_var]) >>
  qexists_tac `mstore b w (update_var v w s)` >>
  simp[run_inst_seq_def, GSYM mk_inst_def] >>
  conj_tac
  >- (`copy_prefix loc a b 1 s (0+1)
        (mstore (b+32*0) (copy_runtime_word loc s (a+n2w 0))
          (update_var v w s))` by
        (irule copy_prefix_extend >> simp[copy_prefix_update_var, copy_prefix_zero]) >>
      gvs[Abbr `w`, Abbr `v`, wordsTheory.WORD_ADD_0]) >>
  simp[immutableMemoryFrameTheory.immutable_mstore_capacity, update_var_def] >>
  simp[mstore_def, write_memory_with_expansion_def, lookup_var_def] >>
  rpt strip_tac >> simp[FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem storage_unwrap_word_code_path[local]:
  (opc = SLOAD \/ opc = TLOAD) /\
  do v <- emit_op opc [src]; emit_void MSTORE [dst; v] od sa = (u,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_path ctx func s 0 (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc` by
    (Cases_on `opc = SLOAD` >> gvs[is_terminator_def]) >>
  qpat_x_assum `do v <- _; _ od _ = _` mp_tac >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  fs[emitted_insts_def] >>
  fs[rich_listTheory.DROP_APPEND1] >>
  drule_at (Pos last) tuple_run_inst_seq_gas_path >>
  simp[mk_inst_def, is_terminator_def] >> disch_then irule >>
  gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
  simp[rich_listTheory.DROP_APPEND1, mk_inst_def]
QED

Theorem storage_unwrap_word_content_path[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
     emit_void MSTORE [dst; v] od sa = (u,sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  b+32 < 2**256 /\ fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z. gas_path ctx func s 0 (OK z) /\ copy_prefix loc a b 1 s 1 z /\
    LENGTH s.vs_memory <= LENGTH z.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all storage_unwrap_word_run >> strip_tac >>
  `gas_path ctx func s 0 (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (drule_at (Pos last) storage_unwrap_word_code_path >>
     disch_then irule >> simp[] >>
     qexistsl_tac [`dst`, `if loc = LocStorage then SLOAD else TLOAD`, `src`] >>
     Cases_on `loc = LocStorage` >> gvs[]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule storage_copy_word_layout >> simp[same_blocks_def]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[copy_prefix_idx, lookup_var_def]
QED

Theorem storage_unwrap_suffix_content_path[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  (if n = 1 then
     do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
        emit_void MSTORE [dst; v] od
   else do compile_word_copy_loop src dst n loc LocMemory F; return () od)
    sa = (u,sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  n < 2**256 /\ b+32*n < 2**256 /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z. gas_path ctx func s 0 (OK z) /\ copy_prefix loc a b n s n z /\
    LENGTH s.vs_memory <= LENGTH z.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  Cases_on `n = 1`
  >- (fs[] >> irule storage_unwrap_word_content_path >> simp[] >>
      qexistsl_tac [`dst`, `src`] >> gvs[] >> metis_tac[]) >>
  fs[] >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  mp_tac (storageCopyGasPathTheory.compile_storage_copy_content_capacity_path
    |> Q.SPEC `F`
    |> CONV_RULE (RAND_CONV (REWR_CONV (GSYM ETA_AX)))
    |> Q.SPEC `(ctx,func)`) >>
  simp[gas_marked_path_def] >> disch_then irule >>
  simp[] >> metis_tac[]
QED

Theorem storage_unwrap_suffix_value_path[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  (if n = 1 then
     do value <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
        emit_void MSTORE [dst; value] od
   else do compile_word_copy_loop src dst n loc LocMemory F; return () od)
    mid = (result,sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at mid x) /\
  stmt_state_rel ctx func cenv cx es u /\
  storage_holds cx (loc = LocTransient) t (Value v) a es u /\
  evaluate_type (get_tenv cx) t = SOME tv /\ n = type_slot_size tv /\
  eval_operand src u = SOME a /\ eval_operand dst u = SOME w /\
  n < 2**256 /\ w2n w + 32*n < 2**256 /\ fn_has_code mid sb func /\
  ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
  u.vs_inst_idx = LENGTH mid.cs_current_insts ==>
  ?z. gas_path ctx func u 0 (OK z) /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    copy_static z = copy_static u /\
    (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
    LENGTH u.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off+len <= w2n w \/ w2n w + type_memory_size tv <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\ eval_operand dst z = SOME w
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `eval_operand dst u = SOME (n2w (w2n w))` by simp[] >>
  drule_all storage_unwrap_suffix_content_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `copy_prefix (if loc = LocTransient then LocTransient else LocStorage)
     a (w2n w) (type_slot_size tv) u (type_slot_size tv) z` by
    (Cases_on `loc = LocTransient` >> gvs[]) >>
  drule_all copy_buffer_storage_contents >> strip_tac >>
  `copy_static z = copy_static u` by gvs[copy_prefix_def] >>
  `eval_operand dst z = SOME w` by
    (drule storage_copy_operand_preserved >>
     disch_then (qspecl_then [`mid`, `dst`] mp_tac) >> simp[]) >>
  qexists_tac `z` >>
  gvs[copy_prefix_def, valueEncodingPropsTheory.type_memory_size_slots] >> metis_tac[]
QED

Theorem storage_unwrap_typed_suffix_path[local]:
  !loc tv src dst mid result sb ctx func cenv cx es u t v a w.
  (loc = LocStorage \/ loc = LocTransient) /\
  (if type_slot_size tv = 1 then
     do value <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
        emit_void MSTORE [dst; value] od
   else do compile_word_copy_loop src dst (type_slot_size tv) loc LocMemory F;
           return () od) mid = (result,sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at mid x) /\
  stmt_state_rel ctx func cenv cx es u /\
  storage_holds cx (loc = LocTransient) t (Value v) a es u /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  eval_operand src u = SOME a /\ eval_operand dst u = SOME w /\
  type_slot_size tv < 2**256 /\ w2n w + 32*type_slot_size tv < 2**256 /\
  fn_has_code mid sb func /\ ~u.vs_halted /\
  u.vs_current_bb = mid.cs_current_bb /\
  u.vs_inst_idx = LENGTH mid.cs_current_insts ==>
  ?z. gas_path ctx func u 0 (OK z) /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    copy_static z = copy_static u /\
    (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
    LENGTH u.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off+len <= w2n w \/ w2n w + type_memory_size tv <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\ eval_operand dst z = SOME w
Proof
  rpt gen_tac >> strip_tac >>
  irule storage_unwrap_suffix_value_path >> simp[] >>
  qexistsl_tac [`a`, `cenv`, `cx`, `es`, `loc`, `src`, `t`] >>
  simp[] >> first_assum ACCEPT_TAC
QED

Theorem storage_unwrap_layout_facts[local]:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  ~is_word_type t /\ fn_has_code sm sb func ==>
  ?buf mid.
    compile_alloc_buffer (type_memory_bytes cenv t) sm = (buf,mid) /\
    (if (type_memory_bytes cenv t + 31) DIV 32 = 1 then
       do value <- emit_op (if p.ptr_location = LocStorage then SLOAD else TLOAD)
                     [p.ptr_operand]; emit_void MSTORE [buf.buf_operand; value] od
     else do compile_word_copy_loop p.ptr_operand buf.buf_operand
               ((type_memory_bytes cenv t + 31) DIV 32) p.ptr_location LocMemory F;
             return () od) mid = ((),sb) /\
    op = buf.buf_operand /\ fn_has_code sm mid func /\ fn_has_code mid sb func /\
    sm.cs_next_var <= mid.cs_next_var /\ mid.cs_next_id <= sb.cs_next_id
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  `compile_ensure_in_memory p.ptr_operand p.ptr_location
     (type_memory_bytes cenv t) ((type_memory_bytes cenv t + 31) DIV 32)
     cenv.ce_is_ctor cenv.ce_imm_alloca sm = (op,sb)` by
    (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
     Cases_on `p.ptr_location` >> gvs[unwrap_value_def]) >>
  qpat_x_assum `unwrap_value _ _ _ = _` kall_tac >>
  qpat_x_assum `compile_ensure_in_memory _ _ _ _ _ _ _ = _` mp_tac >>
  drule ensure_storage_memory_layout >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  gnvs[] >> rename1 `compile_alloc_buffer _ sm = (buf,mid)` >>
  `cs_extends sm mid` by
    metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `cs_extends mid cs''` by
    (irule storage_copy_suffix_extends >>
     qexistsl_tac [`buf.buf_operand`, `p.ptr_location`,
       `(type_memory_bytes cenv t + 31) DIV 32`, `p.ptr_operand`, `()`] >>
     gvs[comp_ignore_bind_def]) >>
  `ci_mono sm mid` by
    (qspecl_then [`type_memory_bytes cenv t`, `sm`] mp_tac
       ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono mid cs''` by
    (irule storage_copy_suffix_ci_mono >>
     qexistsl_tac [`buf.buf_operand`, `p.ptr_location`,
       `(type_memory_bytes cenv t + 31) DIV 32`, `p.ptr_operand`, `()`] >>
     gvs[comp_ignore_bind_def]) >>
  gvs[comp_ignore_bind_def, ci_mono_def] >> metis_tac[fn_has_code_split]
QED

Theorem storage_unwrap_type_facts[local]:
  post_value_type cenv e = expr_type e /\
  vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
    type_memory_bytes cenv t = type_memory_size tvt /\
    type_memory_size tvt < 2**64) ==>
  t = expr_type e /\ stmt_state_rel ctx func cenv cx es' s /\
  ?a tv. eval_operand p.ptr_operand s = SOME a /\
    storage_holds cx (p.ptr_location = LocTransient) t (Value v) a es' s /\
    evaluate_type (get_tenv cx) t = SOME tv /\
    type_memory_bytes cenv t = type_memory_size tv /\
    type_memory_size tv < 2**64 /\
    type_memory_bytes cenv t < dimword (:256) /\
    (type_memory_bytes cenv t + 31) DIV 32 = type_slot_size tv /\
    type_slot_size tv < 2**256
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `t = expr_type e /\ stmt_state_rel ctx func cenv cx es' s` by
    (Cases_on `p.ptr_location` >> gvs[vv_post_def, vv_holds_def]) >> simp[] >>
  `?a. eval_operand p.ptr_operand s = SOME a /\
       storage_holds cx (p.ptr_location = LocTransient) t (Value v) a es' s` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     Cases_on `p.ptr_location` >> gvs[vv_post_def, vv_holds_def]) >>
  `?tv. evaluate_type (get_tenv cx) t = SOME tv` by
    (gvs[storage_holds_def] >> metis_tac[]) >>
  `type_memory_bytes cenv t = type_memory_size tv /\
    type_memory_size tv < 2**64` by metis_tac[] >>
  qexistsl_tac [`a`, `tv`] >> simp[] >>
  gvs[valueEncodingPropsTheory.type_memory_size_slots, wordsTheory.dimword_def] >>
  decide_tac
QED

Theorem storage_unwrap_buffer_post_transport[local]:
  !ctx func cenv cx e es sa sm mid sb s0 es' v t p s u z tv buf w.
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= mid.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < mid.cs_next_id /\
    mid.cs_next_id <= sb.cs_next_id /\
    stmt_state_rel ctx func cenv cx es' u /\ u.vs_memory = s.vs_memory /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sm.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n w) (type_memory_bytes cenv t) b len) /\
    (!name b len. local_region cenv es'.scopes u name b len ==>
       regions_disjoint (w2n w) (type_memory_bytes cenv t) b len) /\
    compile_alloc_buffer (type_memory_bytes cenv t) sm = (buf,mid) /\
    fn_has_code sm mid func /\
    FLOOKUP u.vs_allocas sm.cs_next_id =
      SOME (w2n w,type_memory_bytes cenv t) /\
    copy_static z = copy_static u /\
    (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
    LENGTH u.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off + len <= w2n w \/ w2n w + type_memory_size tv <= off ==>
       mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
    t = expr_type e /\ type_memory_bytes cenv t = type_memory_size tv /\
    ~is_word_type t /\ evaluate_type (get_tenv cx) t = SOME tv /\
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\
    eval_operand buf.buf_operand z = SOME w ==>
    expr_post ctx func cenv cx e es sa sb s0 es' v buf.buf_operand z
Proof
  rpt gen_tac >> strip_tac >>
  `post_value_type cenv e = expr_type e` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[vv_post_def, vv_holds_def] >> rpt strip_tac >>
     gvs[post_value_type_bytestring]) >>
  drule_all buffer_alloc_code >> strip_tac >>
  `~is_word_type (expr_type e)` by metis_tac[] >>
  irule copy_buffer_post_transport >> simp[] >>
  qexistsl_tac [`mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv t))]
                  [STRING #"%" (toString sm.cs_next_var)]`,
               `mid`, `s`, `sm`, `type_memory_bytes cenv t`, `tv`, `u`,
               `LocatedValue t p`] >>
  gvs[mk_inst_def, arithmeticTheory.ADD_COMM] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem unwrap_storage_copy_path:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op s.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    ~is_word_type t /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
           type_memory_bytes cenv t = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all storage_unwrap_layout_facts >> strip_tac >>
  drule_all storage_unwrap_type_facts >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  drule_all alloc_buffer_source_path >> strip_tac >>
  `~u.vs_halted` by metis_tac[gas_path_normal] >>
  `storage_holds cx (p.ptr_location = LocTransient) t (Value v) a es' u` by
    (qpat_x_assum `storage_holds _ _ _ _ _ _ s` mp_tac >>
     simp[storage_holds_def]) >>
  `!x. p.ptr_operand = Var x \/ buf.buf_operand = Var x ==>
       not_fresh_at mid x` by
    (gen_tac >> strip_tac
     >- (irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `sm` >> simp[]) >> fs[]) >>
  `w2n w + 32 * type_slot_size tv < 2**256` by
    (fs[valueEncodingPropsTheory.type_memory_size_slots, wordsTheory.dimword_def]) >>
  `?z. gas_path ctx func u 0 (OK z) /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    copy_static z = copy_static u /\
    (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
    LENGTH u.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off+len <= w2n w \/ w2n w + type_memory_size tv <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\
    eval_operand buf.buf_operand z = SOME w` by
    (irule storage_unwrap_typed_suffix_path >>
     simp[] >> qexistsl_tac [`a`, `cenv`, `cx`, `es'`, `p.ptr_location`,
                            `p.ptr_operand`, `t`] >>
     simp[] >> conj_tac
     >- (qpat_x_assum `!x. p.ptr_operand = Var x \/ buf.buf_operand = Var x ==> _`
           mp_tac >> simp[]) >>
     qpat_x_assum `(if _ then _ else _) mid = _` mp_tac >> simp[]) >>
  `expr_post ctx func cenv cx e es sa sb s0 es' v buf.buf_operand z` by
    (irule storage_unwrap_buffer_post_transport >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl_tac [`mid`, `p`, `s`, `sm`, `t`, `tv`, `u`, `w`] >>
     asm_rewrite_tac [] >> simp[]) >>
  qexists_tac `z` >> conj_tac
  >- (`gas_path ctx func s (0+0) (OK z)` suffices_by simp[] >>
      irule gas_path_then >> qexists_tac `u` >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ z` mp_tac >> simp[]) >>
  simp[]
QED

Theorem unwrap_runtime_code_copy_path:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op s.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ ~is_word_type t /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
           type_memory_bytes cenv t = type_memory_size tvt) /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  drule_all runtime_code_copy_run_post >> strip_tac >>
  drule_all runtime_code_copy_seq_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `z with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[]
QED

Theorem ctor_copy_run_control[local]:
  run_inst_seq code s = OK t /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code ==>
  t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb
Proof
  strip_tac >>
  irule (SRULE [] (Q.ISPEC
    `\s:venom_state. (s.vs_halted,s.vs_current_bb)`
    run_inst_seq_preserves_field)) >>
  qexists_tac `code` >> simp[] >> rpt strip_tac >> fs[EVERY_MEM] >>
  metis_tac[venomInstProofsTheory.step_preserves_halted,
            venomInstProofsTheory.step_preserves_control_flow, step_inst_non_invoke]
QED

Theorem ctor_copy_memory_path[local]:
  !n off st st' s a b ctx func imm src dst.
  compile_imm_copy_to_memory T imm src dst n off st = ((),st') /\
  copy_old_operand st src /\ copy_old_operand st dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
    copy_old_operand st region) /\ fn_has_code st st' func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u. gas_path ctx func s 0 (OK u) /\ ~u.vs_halted /\
    u.vs_current_bb = st'.cs_current_bb /\
    u.vs_inst_idx = LENGTH st'.cs_current_insts /\
    u.vs_memory = (immutable_transfers F T a b n off s).vs_memory /\
    copy_static u = copy_static s /\
    (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >> drule_all copy_ctor_run >> strip_tac >>
  drule code_ctor_copy_insts >> strip_tac >>
  `emitted_insts st st' = is` by
    simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is /\
   FILTER (\i. i.inst_opcode = GAS) is = []` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> conj_tac >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> gvs[is_terminator_def]) >>
  fs[copy_runtime_frame_def] >> drule_all ctor_copy_run_control >> strip_tac >>
  qexists_tac `zz with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  fs[exprSimStorageCopyTheory.copy_static_def, lookup_var_def] >>
  gvs[same_blocks_def, fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) tuple_run_inst_seq_gas_path >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  simp[DROP_APPEND]
QED

Theorem ctor_copy_endpoint_post[local]:
  vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
  local_ptrs_reserved cenv sa /\ cenv.ce_is_ctor /\ ~is_word_type t /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= mid.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < mid.cs_next_id /\
  mid.cs_next_id <= sb.cs_next_id /\
  compile_alloc_buffer (type_memory_bytes cenv t) sm = (buf,mid) /\
  fn_has_code sm mid func /\
  immutable_holds cenv cx t (Value v) a es' s /\
  evaluate_type (get_tenv cx) t = SOME tv /\ t = expr_type e /\
  type_memory_bytes cenv t = type_memory_size tv /\
  stmt_state_rel ctx func cenv cx es' u /\ u.vs_memory = s.vs_memory /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!aid b len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
     regions_disjoint (w2n w) (type_memory_bytes cenv t) b len) /\
  (!name b len. local_region cenv es'.scopes u name b len ==>
     regions_disjoint (w2n w) (type_memory_bytes cenv t) b len) /\
  eval_operand buf.buf_operand u = SOME w /\
  FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_bytes cenv t) /\
  w2n w + type_memory_bytes cenv t < dimword (:256) /\
  (?bp. buf.buf_operand = Var bp /\ not_fresh_at mid bp) /\
  z.vs_memory = (immutable_transfers F T a w (type_slot_size tv) 0 u).vs_memory /\
  copy_static z = copy_static u /\
  (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) ==>
  expr_post ctx func cenv cx e es sa sb s0 es' v buf.buf_operand z
Proof
  strip_tac >>
  `post_value_type cenv e = expr_type e` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[vv_post_def, vv_holds_def] >> rpt strip_tac >>
     gvs[post_value_type_bytestring]) >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv t))]
       [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func)` by
    metis_tac[buffer_alloc_code] >>
  `immutable_holds cenv cx t (Value v) a es' u` by
    metis_tac[immutable_holds_memory_cong] >>
  `regions_disjoint (w2n a) (type_memory_size tv)
      (w2n w) (type_memory_size tv)` by
    (irule immutable_holds_alloca_disjoint >>
     qexistsl_tac [`cenv`, `ctx`, `cx`, `es'`, `func`] >>
     goal_assum (drule_at Any) >> simp[mk_inst_def] >>
     qpat_assum `MEM (mk_inst _ _ _ _) _` (irule_at Any) >> gvs[mk_inst_def]) >>
  `w2n w + type_memory_size tv < dimword (:256)` by metis_tac[] >>
  drule_all copy_ctor_contents >> strip_tac >>
  `eval_operand buf.buf_operand z = SOME w` by
    (qsuff_tac `eval_operand buf.buf_operand z = eval_operand buf.buf_operand u`
     >- gvs[] >>
     irule exprSimStorageCopyTheory.storage_copy_operand_preserved >> simp[] >>
     qexists_tac `mid` >> simp[]) >>
  irule copy_buffer_post_transport >>
  qpat_assum `t = expr_type e` (fn th => rewrite_tac[GSYM th]) >>
  simp[] >> goal_assum (drule_at Any) >> simp[mk_inst_def, SF SFY_ss] >>
  qexists_tac `mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv t))]
       [STRING #"%" (toString sm.cs_next_var)]` >>
  qexistsl_tac [`mid`, `s`, `sm`, `u`, `LocatedValue t p`] >>
  simp[mk_inst_def] >> gnvs[] >> metis_tac[]
QED

Theorem unwrap_ctor_code_copy_path:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op s.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ cenv.ce_is_ctor /\ ~is_word_type t /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
           type_memory_bytes cenv t = type_memory_size tvt) /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def, contextTheory.compile_ensure_in_memory_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  gvs[] >> rename1 `compile_alloc_buffer _ sm = (buf,mid)` >>
  `t = expr_type e` by gvs[vv_post_def, vv_holds_def] >>
  `?a. eval_operand p.ptr_operand s = SOME a /\
       immutable_holds cenv cx t (Value v) a es' s` by
    gvs[vv_post_def, vv_holds_def] >>
  `?tv. evaluate_type (get_tenv cx) t = SOME tv` by
    (gvs[immutable_holds_def] >> metis_tac[]) >>
  `val_wf tv v /\ w2n a + type_memory_size tv < dimword (:256)` by
    (drule_all immutable_holds_bounds >> simp[]) >>
  `type_memory_bytes cenv t = type_memory_size tv` by metis_tac[] >>
  `type_memory_bytes cenv t < dimword (:256)` by decide_tac >>
  `ci_mono sm mid` by
    (qspecl_then [`type_memory_bytes cenv t`, `sm`] mp_tac
       ci_mono_compile_alloc_buffer >> simp[]) >>
  rename1 `compile_imm_copy_to_memory _ _ _ _ _ _ mid = (_,sc)` >>
  `ci_mono mid sc` by
    (qpat_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     metis_tac[ci_mono_compile_imm_copy_to_memory, pairTheory.SND]) >>
  `cs_extends sm mid /\ cs_extends mid sc /\
   sm.cs_next_var <= mid.cs_next_var /\ mid.cs_next_id <= sc.cs_next_id` by
    gvs[ci_mono_def] >>
  `fn_has_code sm mid func /\ fn_has_code mid sc func` by
    metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx func cenv cx es' s` by fs[vv_post_def] >>
  `immutable_base_zero cenv s` by fs[stmt_state_rel_def] >>
  drule_all alloc_buffer_source_path >> strip_tac >>
  suspend "ctor_counted_suffix"
QED

Resume unwrap_ctor_code_copy_path[ctor_counted_suffix]:
  `copy_old_operand mid p.ptr_operand /\ copy_old_operand mid buf.buf_operand` by
    (rw[copy_old_operand_def] >> gvs[] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `!region. cenv.ce_imm_alloca = SOME region ==>
      eval_operand region u = SOME 0w /\ copy_old_operand mid region` by
    (rpt strip_tac >>
     `eval_operand region s = SOME 0w` by fs[immutable_base_zero_def] >>
     `!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x` by
       metis_tac[local_ptrs_reserved_imm_base] >>
     Cases_on `region` >> gvs[eval_operand_def, copy_old_operand_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `(type_memory_bytes cenv t + 31) DIV 32 = type_slot_size tv` by
    (simp[valueEncodingPropsTheory.type_memory_size_slots] >> decide_tac) >>
  drule_all ctor_copy_memory_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path ctx func u 0 (OK z)` >>
  qexists_tac `z` >> simp[] >> conj_tac
  >- metis_tac[gas_path_then, arithmeticTheory.ADD_CLAUSES] >>
  `z.vs_memory = (immutable_transfers F T a w (type_slot_size tv) 0 u).vs_memory` by
    metis_tac[] >>
  SUBGOAL_THEN ``?bp. buf.buf_operand = Var bp /\ not_fresh_at mid bp`` assume_tac
  >- metis_tac[] >>
  drule_all ctor_copy_endpoint_post >> simp[]
QED

Finalise unwrap_ctor_code_copy_path

(* unwrap_value_sim's counted form: every value_vv's code, one path. *)
Theorem unwrap_value_path:
  !ctx func cenv cx e es sa sm sb s0 es' v vv op s.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv vv sm = (op, sb) /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
           ~is_word_type (expr_type e) ==>
           type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) vv s /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  Cases_on `vv`
  >- (gvs[unwrap_value_def, comp_return_def] >> qexists_tac `s` >>
      simp[cj 1 gas_path_rules] >> metis_tac[expr_post_of_vv_post_stack]) >>
  rename1 `LocatedValue t p` >>
  RULE_ASSUM_TAC (REWRITE_RULE [contextTheory.vv_operand_def]) >>
  Cases_on `p.ptr_location = LocCalldata`
  >- gvs[vv_post_calldata] >>
  Cases_on `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient`
  >- (`t = expr_type e` by
        (qpat_x_assum `_ \/ _` strip_assume_tac >>
         gvs[vv_post_def, vv_holds_def]) >>
      Cases_on `is_word_type t`
      >- (irule unwrap_storage_word_path >> gvs[] >> metis_tac[]) >>
      irule unwrap_storage_copy_path >> gvs[] >> metis_tac[]) >>
  Cases_on `p.ptr_location = LocCode`
  >- (`t = expr_type e` by gvs[vv_post_def, vv_holds_def] >>
      reverse (Cases_on `is_word_type t`)
      >- (Cases_on `cenv.ce_is_ctor`
          >- (irule unwrap_ctor_code_copy_path >> gvs[] >> metis_tac[]) >>
          irule unwrap_runtime_code_copy_path >> gvs[] >> metis_tac[]) >>
      Cases_on `cenv.ce_is_ctor`
      >- (irule unwrap_ctor_immutable_word_path >> gvs[] >> metis_tac[]) >>
      irule unwrap_runtime_immutable_word_path >>
      gvs[unwrap_value_def, contextTheory.compile_ptr_load_def,
          contextTheory.compile_imm_load_word_def] >> metis_tac[]) >>
  `p.ptr_location = LocMemory` by (Cases_on `p.ptr_location` >> gvs[]) >>
  drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_memory_marked_read >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  impl_tac >- simp[] >>
  rw[gas_marked_exec_def, gas_marked_path_def] >>
  first_x_assum (qspec_then `[]` mp_tac) >>
  simp[read_result_def, return_def] >> strip_tac >> gvs[] >>
  goal_assum drule >> simp[]
QED

(* The counted read suffix: read_result's source step reads no gas, and
   unwrap_value's code runs along a GAS-free path. *)
Theorem unwrap_value_marked_read:
  !ctx func cenv cx e es sa sm sb s0 ee tv vv op s.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv vv sm = (op, sb) /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
           ~is_word_type (expr_type e) ==>
           type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) /\
    vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?v u. gas_marked_exec F (ctx,func) (read_result cx tv) (ee,s)
            [] (INL v) ee (OK u) /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `read_result cx tv ee` >> rename1 `_ = (res, ee')` >>
  `ee' = ee` by metis_tac[read_result_state] >> gvs[] >>
  reverse (Cases_on `res`)
  >- metis_tac[vv_post_failed_read] >>
  rename1 `read_result cx tv ee = (INL v, ee)` >>
  drule_all vv_post_read_result >> strip_tac >>
  drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_value_path >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl_tac [`v`, `u`] >> simp[] >>
  simp[gas_marked_exec_def, gas_marked_path_def] >>
  metis_tac[read_result_gas_obs, APPEND]
QED

(* unwrap_value's step: expr_vv_sim gives expr_sim.  compile_expr's
   fragment ends in vv_post, and unwrap_value's code takes that to
   expr_post. *)
Theorem expr_sim_of_vv_sim:
  !ctx func cenv cx ty e es.
    post_value_type cenv e = expr_type e /\
    expr_vv_sim ctx func cenv cx ty e es /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
           ~is_word_type (expr_type e) ==>
           type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) ==>
    expr_sim ctx func cenv cx ty e es
Proof
  rw[expr_sim_def] >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty e sa` >> rename1 `_ = (vv, sm)` >>
  simp[] >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    (drule (cj 1 exprOperandVarTheory.compiler_compile_var) >> simp[]) >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[forced_expr_admissible_raw] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` mp_tac >>
  simp[expr_vv_sim_def] >>
  disch_then (qspecl_then [`sa`, `sm`, `vv`, `s0`] mp_tac) >>
  simp[] >>
  rewrite_tac[gas_outcome_def] >> strip_tac >>
  qexists_tac `marks`
  >- (disj1_tac >> gvs[gas_summary_at_def]
      >- (rename1 `vv_post _ _ _ _ _ _ _ _ _ _ tv vv u` >>
          `~u.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
          `MAP FDOM es.scopes = MAP FDOM (es_end with gas_obs := []).scopes` by
            (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
               (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
             strip_tac >> first_x_assum (qspec_then `[]` assume_tac) >>
             drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >>
             simp[]) >>
          drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_value_marked_read >>
          disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
          impl_tac >- simp[] >> strip_tac >>
          rename1 `gas_marked_exec F _ (read_result _ _) _ [] _ _ (OK u2)` >>
          qexistsl_tac [`INL v`, `es_end with gas_obs := []`, `OK u2`] >>
          simp[] >>
          `marks = marks ++ []` by simp[] >>
          pop_assum SUBST1_TAC >> irule gas_marked_exec_bind_normal >>
          goal_assum drule >> simp[]) >>
      Cases_on `res`
      >- (Cases_on `r` >> gvs[expr_exit_def]) >>
      rename1 `expr_exit (INR exc) r` >>
      `expr_res_ok (INR exc : value + exception)` by
        (Cases_on `exc` >> Cases_on `r` >>
         gvs[expr_exit_def, expr_res_ok_def, AllCaseEqs()] >>
         Cases_on `e'` >> gvs[expr_exit_def, expr_res_ok_def]) >>
      qexistsl_tac [`INR exc`, `es_end`, `r`] >>
      simp[GSYM expr_exit_exception_transport] >>
      irule gas_marked_exec_bind_exception >> goal_assum drule) >>
  disj2_tac >> metis_tac[force_exempt_cert]
QED
