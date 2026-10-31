(*
 * unwrap_value's step of the expression simulation (#636)
 *
 * lower_value is compile_expr followed by unwrap_value, which turns the
 * value_vv compile_expr hands out into an operand: none for a StackValue
 * or an aggregate in memory, a load for a word behind a pointer, a copy
 * into a buffer for an aggregate elsewhere.  expr_sim_of_vv_sim sequences
 * compile_expr's fragment, which ends in vv_post (expr_vv_sim), with
 * unwrap_value's, which takes vv_post to expr_post (unwrap_value_sim).
 *
 * TOP-LEVEL:
 *   expr_sim_of_vv_sim — expr_vv_sim gives expr_sim
 *   expr_sim_of_vv_sim_buffer — the same for an expression lowered to a
 *                        pointer into memory, without the cheated cases
 *   unwrap_value_sim   — unwrap_value's code takes vv_post to expr_post,
 *                        one lemma per form of value_vv:
 *                        expr_post_of_vv_post_stack,
 *                        unwrap_memory_sim (expr_post_of_vv_post_memory,
 *                        and unwrap_memory_word_sim's MLOAD),
 *                        unwrap_runtime_immutable_word_sim (DLOAD),
 *                        unwrap_storage_word_sim (SLOAD/TLOAD),
 *                        vv_post_calldata (no calldata pointers)
 *
 * Helpers: compile_expr_extends (exprLoweringProps' compile_expr_grows),
 *   compile_ensure_in_memory_extends, unwrap_value_extends,
 *   expr_post_of_vv_post_load, step_DLOAD, immutable_holds_dload,
 *   storage_word_load, storage_holds_load
 *
 * Cheated, each with its reason at the lemma:
 *   unwrap_ctor_immutable_word_sim — constructor immutable word-load proof
 *   unwrap_copy_sim    — the copy of an aggregate out of storage or code
 *)

Theory exprSimUnwrap
Ancestors
  list finite_map
  exprSim exprLowering compileEnv immutableEncoding vyperAST vyperInterpreter
  vyperState
  loweringSlice fragExec freshWrites venomInst venomExecSemantics venomState
  valueEncoding valueEncodingProofs vyperTypeValues vyperStorage vyperValue
  vyperLookupStorage
Libs
  pairLib

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

Theorem compile_imm_load_word_appends[local]:
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
     contextTheory.compile_word_copy_loop_def,
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
Theorem vv_post_read_result:
  !func cenv cx e es sa sb s0 es' tv v vv s.
    read_result cx tv es' = (INL v, es') ==>
    (vv_post func cenv cx e es sa sb s0 es' tv vv s <=>
     vv_post func cenv cx e es sa sb s0 es' (Value v) vv s)
Proof
  rpt strip_tac >> Cases_on `vv` >>
  simp[vv_post_def, vv_holds_def, vv_at_def, storage_holds_def,
       immutable_holds_def, read_result_def, return_def]
QED

(* ===== unwrap_value's code ===== *)

(* unwrap_value's code, run where compile_expr's code ends, takes vv_post to
   expr_post.  One lemma per form of value_vv. *)

(* A StackValue: no code. *)
Theorem expr_post_of_vv_post_stack:
  !func cenv cx e es sa sb s0 es' v t op s.
    vv_post func cenv cx e es sa sb s0 es' (Value v) (StackValue t op) s ==>
    expr_post func cenv cx e es sa sb s0 es' v op s
Proof
  rw[vv_post_def, expr_post_def, vv_holds_def, vv_at_def,
     read_result_def, return_def]
QED

(* An aggregate in memory: the pointer is the operand, no code. *)
Theorem expr_post_of_vv_post_memory:
  !func cenv cx e es sa sb s0 es' v t p s.
    vv_post func cenv cx e es sa sb s0 es' (Value v) (LocatedValue t p) s /\
    p.ptr_location = LocMemory /\ ~is_word_type t ==>
    expr_post func cenv cx e es sa sb s0 es' v p.ptr_operand s
Proof
  rw[vv_post_def, expr_post_def, vv_holds_def, vv_at_def] >>
  gvs[read_result_def, return_def, expr_val_rel_def, expr_val_at_def] >>
  metis_tac[]
QED

(* The end of a one-instruction load of a word: the loaded word in a fresh
   variable, nothing else changed. *)
Theorem expr_post_of_vv_post_load:
  !func cenv cx e es sa sm sb s0 es' v t p op s1 s w.
    vv_post func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s1 /\
    is_word_type (expr_type e) /\ sa.cs_next_var <= sm.cs_next_var /\
    stmt_state_rel func cenv cx es' s /\ eval_operand op s = SOME w /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
           w = typed_val_to_w256 tvt v) /\
    (!x w'. not_fresh_at sm x /\ lookup_var x s1 = SOME w' ==>
            lookup_var x s = SOME w') /\
    (!aid b. FLOOKUP s1.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b) /\
    s.vs_memory = s1.vs_memory ==>
    expr_post func cenv cx e es sa sb s0 es' v op s
Proof
  rw[expr_post_def]
  >~ [`expr_val_rel`] >- gvs[expr_val_rel_def]
  >~ [`expr_val_at`] >- simp[expr_val_at_def]
  >~ [`lookup_var x s`]
  >- (fs[vv_post_def] >> metis_tac[not_fresh_at_mono])
  >~ [`FLOOKUP s.vs_allocas`] >- fs[vv_post_def]
  >~ [`locals_kept`]
  >- (fs[vv_post_def] >> metis_tac[locals_kept_mem_tail]) >>
  fs[vv_post_def] >> metis_tac[]
QED

(* A word in memory: an MLOAD. *)
Theorem unwrap_memory_word_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    emit_op MLOAD [p.ptr_operand] sm = (op, sb) /\
    p.ptr_location = LocMemory /\ is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
    frag_exec ctx sm sb
      (\s. vv_post func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post func cenv cx e es sa sb s0 es' v op s) R
Proof
  rpt strip_tac >> irule frag_exec_pointwise >> rw[] >>
  rename1 `vv_post _ _ _ _ _ _ _ _ _ _ _ s1` >>
  `t = expr_type e /\
   ?w. eval_operand p.ptr_operand s1 = SOME w /\
       !tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
             mem_word_at (w2n w) s1.vs_memory = typed_val_to_w256 tvt v` by
    (gvs[vv_post_def, vv_holds_def, read_result_def, return_def] >>
     metis_tac[]) >>
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
  qspecl_then [`func`, `cenv`, `cx`, `e`, `es`, `sa`, `sm`, `sb`, `s0`, `es'`,
               `v`, `expr_type e`, `p`, `op`, `s1`, `s`, `mload (w2n w) s1`]
    mp_tac expr_post_of_vv_post_load >>
  impl_tac
  >- (asm_rewrite_tac[] >> rpt strip_tac >>
      fs[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload]) >>
  simp[]) >>
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
  rw[venomExecSemanticsTheory.step_inst_base_def,
     venomExecSemanticsTheory.exec_read1_def]
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
  !func cenv cx es s t v w.
    stmt_state_rel func cenv cx es s /\ ~cenv.ce_is_ctor /\
    is_word_type t /\ immutable_holds cenv cx t (Value v) w es ==>
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
  gvs[valueEncodingTheory.mem_word_at_def]
QED

(* A word immutable at runtime: a DLOAD. *)
Theorem unwrap_runtime_immutable_word_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    emit_op DLOAD [p.ptr_operand] sm = (op, sb) /\
    p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
    frag_exec ctx sm sb
      (\s. vv_post func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post func cenv cx e es sa sb s0 es' v op s) R
Proof
  rpt strip_tac >> irule frag_exec_pointwise >> rw[] >>
  rename1 `vv_post _ _ _ _ _ _ _ _ _ _ _ s1` >>
  `t = expr_type e /\
   ?w. eval_operand p.ptr_operand s1 = SOME w /\
       immutable_holds cenv cx (expr_type e) (Value v) w es' /\
       stmt_state_rel func cenv cx es' s1` by
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
  qspecl_then [`func`, `cenv`, `cx`, `e`, `es`, `sa`, `sm`, `sb`, `s0`, `es'`,
               `v`, `expr_type e`, `p`, `op`, `s1`, `s`,
               `word_of_bytes T (0w:bytes32)
                  (TAKE 32 (DROP (w2n w) s1.vs_data_section ++
                            REPLICATE 32 0w))`]
    mp_tac expr_post_of_vv_post_load >>
  impl_tac >- (asm_rewrite_tac[] >> rpt strip_tac >> gvs[]) >>
  simp[]) >>
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
      (\s. vv_post func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post func cenv cx e es sa sb s0 es' v op s) R
Proof
  rpt strip_tac >> Cases_on `is_word_type t`
  >- (irule unwrap_memory_word_sim >>
      gvs[unwrap_value_def, contextTheory.compile_ptr_load_def]) >>
  gvs[unwrap_value_def, comp_return_def] >> irule frag_exec_refl >>
  rw[] >> metis_tac[expr_post_of_vv_post_memory]
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

(* At runtime the word a storage or transient load returns is the value's
   (storage_rel, transient_rel). *)
Theorem storage_holds_load[local]:
  !func cenv cx es s t v w tr.
    stmt_state_rel func cenv cx es s /\ is_word_type t /\
    storage_holds cx tr t (Value v) w es ==>
    !tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
          (if tr then tload w s else sload w s) = typed_val_to_w256 tvt v
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  gvs[storage_holds_def, read_result_def, return_def] >>
  gvs[read_storage_slot_def, vyperStorageBackendTheory.get_storage_backend_eq,
      bind_def, lift_option_def, AllCaseEqs(), return_def, raise_def] >>
  qpat_x_assum `option_CASE _ _ _ _ = _` mp_tac >> CASE_TAC >>
  simp[raise_def, return_def] >> strip_tac >> gvs[] >>
  drule_all storage_word_load >> strip_tac >>
  Cases_on `tr` >>
  gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def,
      storage_rel_def, transient_rel_def, sload_def, tload_def,
      vyperStorageBackendTheory.get_storage_def,
      vfmStateTheory.lookup_account_def,
      vfmExecutionTheory.lookup_transient_storage_def]
QED

(* A word in storage or transient storage: an SLOAD or TLOAD. *)
Theorem unwrap_storage_word_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
    frag_exec ctx sm sb
      (\s. vv_post func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post func cenv cx e es sa sb s0 es' v op s) R
Proof
  rpt strip_tac >>
  gvs[unwrap_value_def, contextTheory.compile_ptr_load_def] >> (
  irule frag_exec_pointwise >> rw[] >>
  rename1 `vv_post _ _ _ _ _ _ _ _ _ _ _ s1` >>
  `t = expr_type e /\
   ?w. eval_operand p.ptr_operand s1 = SOME w /\
       storage_holds cx (p.ptr_location = LocTransient) (expr_type e)
         (Value v) w es' /\
       stmt_state_rel func cenv cx es' s1` by
    gvs[vv_post_def, vv_holds_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  `!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
         (if p.ptr_location = LocTransient then tload w s1 else sload w s1) =
         typed_val_to_w256 tvt v` by (
    rpt strip_tac >> drule_then drule storage_holds_load >>
    disch_then drule >> disch_then drule >> simp[]) >>
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
  qspecl_then [`func`, `cenv`, `cx`, `e`, `es`, `sa`, `sm`, `sb`, `s0`, `es'`,
               `v`, `expr_type e`, `p`, `op`, `s1`, `s`,
               `if p.ptr_location = LocTransient then tload w s1
                else sload w s1`]
    mp_tac expr_post_of_vv_post_load >>
  impl_tac >- (asm_rewrite_tac[] >> rpt strip_tac >> gvs[]) >>
  simp[]) >>
  gvs[])
QED

(* A word immutable in the constructor: a load from the immutable buffer.
   Issue #563 supplies the buffer-relative lowering and memory relation;
   the corresponding fragment-execution proof remains admitted here. *)
Theorem unwrap_ctor_immutable_word_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ cenv.ce_is_ctor /\ is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
    frag_exec ctx sm sb
      (\s. vv_post func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post func cenv cx e es sa sb s0 es' v op s) R
Proof
  cheat
QED

(* An aggregate in storage, transient storage or code: a copy into a buffer
   of the expression's own, allocated at instruction id sm.cs_next_id.
   Cheated: the copy-loop simulation remains to be proved for each source
   location.  Issue #563 supplies full-layout immutable relations and
   buffer-relative constructor copies; those are no longer lowering or
   relation blockers. *)
Theorem unwrap_copy_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
     p.ptr_location = LocCode) /\ ~is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id ==>
    frag_exec ctx sm sb
      (\s. vv_post func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post func cenv cx e es sa sb s0 es' v op s) R
Proof
  cheat
QED

(* No value_vv points into calldata. *)
Theorem vv_post_calldata:
  !func cenv cx e es sa sm s0 es' tv t p s.
    p.ptr_location = LocCalldata ==>
    ~vv_post func cenv cx e es sa sm s0 es' tv (LocatedValue t p) s
Proof
  rw[vv_post_def, vv_holds_def]
QED

Theorem unwrap_value_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v vv op R.
    unwrap_value cenv vv sm = (op, sb) /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id ==>
    frag_exec ctx sm sb
      (\s. vv_post func cenv cx e es sa sm s0 es' (Value v) vv s)
      (\s. expr_post func cenv cx e es sa sb s0 es' v op s) R
Proof
  rpt strip_tac >> Cases_on `vv`
  >- (gvs[unwrap_value_def, comp_return_def] >> irule frag_exec_refl >>
      rw[] >> metis_tac[expr_post_of_vv_post_stack]) >>
  rename1 `LocatedValue t p` >>
  Cases_on `p.ptr_location = LocCalldata`
  >- (irule frag_exec_conseq >>
      qexistsl_tac [`\s. F`, `\s. F`, `R`] >>
      gvs[fragExecTheory.frag_exec_false_pre, vv_post_calldata]) >>
  Cases_on `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient`
  >- (Cases_on `is_word_type t`
      >- (irule unwrap_storage_word_sim >> gvs[]) >>
      irule unwrap_copy_sim >> gvs[] >>
      qpat_x_assum `_ \/ _` strip_assume_tac >> simp[]) >>
  Cases_on `p.ptr_location = LocCode`
  >- (Cases_on `is_word_type t` >~ [`~is_word_type t`]
      >- (irule unwrap_copy_sim >> gvs[]) >>
      Cases_on `cenv.ce_is_ctor`
      >- (irule unwrap_ctor_immutable_word_sim >> gvs[]) >>
      irule unwrap_runtime_immutable_word_sim >>
      gvs[unwrap_value_def, contextTheory.compile_ptr_load_def,
          contextTheory.compile_imm_load_word_def]) >>
  `p.ptr_location = LocMemory` by (Cases_on `p.ptr_location` >> gvs[]) >>
  irule unwrap_memory_sim >> simp[]
QED

Theorem vv_post_failed_read[local]:
  !func cenv cx e es sa sm s0 es' raw vv s exc.
    read_result cx raw es' = (INR exc, es') ==>
    ~vv_post func cenv cx e es sa sm s0 es' raw vv s
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
      (\s. vv_post func cenv cx e es sa sm s0 es' raw (LocatedValue t p) s)
      (\s. ?v. res = INL v /\ expr_post func cenv cx e es sa sb s0 es' v op s)
      (expr_exit res)
Proof
  rpt strip_tac >> Cases_on `res`
  >- (rename1 `read_result cx raw es' = (INL v, es')` >>
      drule vv_post_read_result >> strip_tac >>
      irule frag_exec_conseq >>
      qexistsl_tac
        [`\s. vv_post func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s`,
         `\s. expr_post func cenv cx e es sa sb s0 es' v op s`,
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

Theorem expr_exit_exception_transport:
  !exc result.
    expr_res_ok (INR exc : value + exception) ==>
    (expr_exit (INR exc : eval_result + exception) result <=>
     expr_exit (INR exc : value + exception) result)
Proof
  rpt strip_tac >> gvs[expr_res_ok_def] >>
  Cases_on `result` >> simp[expr_exit_def]
QED

Theorem unwrap_read_result_sim[local]:
  !ctx func cenv cx e es sa sm sb s0 es' raw res vv op.
    read_result cx raw es' = (res, es') /\
    unwrap_value cenv vv sm = (op, sb) /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id ==>
    frag_exec ctx sm sb
      (\s. vv_post func cenv cx e es sa sm s0 es' raw vv s)
      (\s. ?v. res = INL v /\ expr_post func cenv cx e es sa sb s0 es' v op s)
      (expr_exit res)
Proof
  rpt strip_tac >> Cases_on `res`
  >- (rename1 `read_result cx raw es' = (INL v, es')` >>
      drule vv_post_read_result >> strip_tac >>
      irule frag_exec_conseq >>
      qexistsl_tac
        [`\s. vv_post func cenv cx e es sa sm s0 es' (Value v) vv s`,
         `\s. expr_post func cenv cx e es sa sb s0 es' v op s`,
         `\r. F`] >>
      simp[] >> irule unwrap_value_sim >> simp[]) >>
  rename1 `read_result cx raw es' = (INR exc, es')` >>
  irule frag_exec_conseq >> qexistsl_tac [`\s. F`, `\s. F`, `\r. F`] >>
  simp[fragExecTheory.frag_exec_false_pre] >> metis_tac[vv_post_failed_read]
QED

(* unwrap_value's step: expr_vv_sim gives expr_sim.  compile_expr's
   fragment ends in vv_post, and unwrap_value's code takes that to
   expr_post. *)
Theorem expr_sim_of_vv_sim:
  !ctx func cenv cx ty e es.
    expr_vv_sim ctx func cenv cx ty e es ==> expr_sim ctx func cenv cx ty e es
Proof
  rw[expr_sim_def] >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty e sa` >> rename1 `_ = (vv, sm)` >>
  simp[] >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  Cases_on `eval_expr cx e es` >> rename1 `_ = (raw, est)` >>
  qpat_x_assum `(do result <- _; _ od) _ = _` mp_tac >>
  simp[bind_def] >>
  Cases_on `raw`
  >- (rename1 `eval_expr cx e es = (INL r, est)` >> simp[] >> strip_tac >>
      drule read_result_state >> strip_tac >> gvs[] >>
      `expr_vv_res_ok (INL r)` by
        (Cases_on `r` >> gvs[expr_vv_res_ok_def, read_result_def,
                             raise_def, expr_res_ok_def]) >>
      qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
        (mp_tac o SIMP_RULE std_ss [expr_vv_sim_def]) >>
      disch_then (qspecl_then [`sa`, `sm`, `vv`, `INL r`, `es'`, `s0`] mp_tac) >>
      simp[] >> strip_tac >>
      irule frag_exec_seq >>
      qexistsl_tac [`\s. vv_post func cenv cx e es sa sm s0 es' r vv s`, `sm`] >>
      simp[] >> conj_tac
      >- (irule frag_exec_conseq >> first_x_assum (irule_at Any) >>
          simp[FUN_EQ_THM]) >>
      irule unwrap_read_result_sim >> simp[]) >>
  rename1 `eval_expr cx e es = (INR exc, est)` >>
  strip_tac >> gvs[] >>
  `expr_vv_res_ok (INR exc)` by gvs[expr_vv_res_ok_def, expr_res_ok_def] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
    (mp_tac o SIMP_RULE std_ss [expr_vv_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `vv`, `INR exc`, `es'`, `s0`] mp_tac) >>
  simp[] >> strip_tac >>
  irule frag_exec_seq >> qexistsl_tac [`\s. F`, `sm`] >> simp[] >>
  conj_tac
  >- (irule frag_exec_conseq >> first_x_assum (irule_at Any) >>
      simp[expr_exit_exception_transport]) >>
  simp[fragExecTheory.frag_exec_false_pre]
QED

(* Memory-buffer forcing uses only the oracle-clean memory boundary. *)
Theorem expr_sim_of_vv_sim_buffer:
  !ctx func cenv cx ty e es.
    expr_vv_sim ctx func cenv cx ty e es /\
    (!sa. ?t p sb. compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
      p.ptr_location = LocMemory /\ ~is_word_type t) /\
    (!tv es'. eval_expr cx e es = (INL tv,es') ==> ?v. tv = Value v) ==>
    expr_sim ctx func cenv cx ty e es
Proof
  rw[expr_sim_def] >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty e sa` >> rename1 `_ = (vv, sm)` >>
  simp[] >> strip_tac >>
  qpat_x_assum `!tv es'. eval_expr _ _ _ = _ ==> _` kall_tac >>
  qpat_x_assum `!sa. ?t p sb. _` (qspec_then `sa` strip_assume_tac) >>
  gvs[] >> rename1 `compile_expr cenv ty e sa = (LocatedValue t p, sm)` >>
  drule compile_expr_extends >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  Cases_on `eval_expr cx e es` >> rename1 `_ = (raw, est)` >>
  qpat_x_assum `(do result <- _; _ od) _ = _` mp_tac >>
  simp[bind_def] >> Cases_on `raw`
  >- (rename1 `eval_expr cx e es = (INL r, est)` >> simp[] >> strip_tac >>
      drule read_result_state >> strip_tac >> gvs[] >>
      `expr_vv_res_ok (INL r)` by
        (Cases_on `r` >> gvs[expr_vv_res_ok_def, read_result_def,
                             raise_def, expr_res_ok_def]) >>
      qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
        (mp_tac o SIMP_RULE std_ss [expr_vv_sim_def]) >>
      disch_then (qspecl_then [`sa`, `sm`, `LocatedValue t p`, `INL r`, `es'`, `s0`] mp_tac) >>
      simp[] >> strip_tac >>
      irule frag_exec_seq >>
      qexistsl_tac [`\s. vv_post func cenv cx e es sa sm s0 es' r (LocatedValue t p) s`, `sm`] >>
      simp[] >> conj_tac
      >- (irule frag_exec_conseq >> first_x_assum (irule_at Any) >>
          simp[FUN_EQ_THM]) >>
      irule unwrap_memory_read_result_sim >> simp[]) >>
  rename1 `eval_expr cx e es = (INR exc, est)` >> strip_tac >> gvs[] >>
  `expr_vv_res_ok (INR exc)` by gvs[expr_vv_res_ok_def, expr_res_ok_def] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
    (mp_tac o SIMP_RULE std_ss [expr_vv_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `LocatedValue t p`, `INR exc`, `es'`, `s0`] mp_tac) >>
  simp[] >> strip_tac >>
  irule frag_exec_seq >> qexistsl_tac [`\s. F`, `sm`] >> simp[] >> conj_tac
  >- (irule frag_exec_conseq >> first_x_assum (irule_at Any) >>
      simp[expr_exit_exception_transport]) >>
  simp[fragExecTheory.frag_exec_false_pre]
QED

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag expr_sim_of_vv_sim_buffer)
  in
    if null axioms andalso null (Thm.hyp expr_sim_of_vv_sim_buffer) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then
      print "MEMORY_FORCE_AUDIT expr_sim_of_vv_sim_buffer OK\n"
    else raise Fail "expr_sim_of_vv_sim_buffer: admitted proof dependency"
  end;
