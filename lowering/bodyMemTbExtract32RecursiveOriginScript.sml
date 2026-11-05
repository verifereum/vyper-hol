Theory bodyMemTbExtract32RecursiveOrigin
Ancestors
  bodyMemTbExtract32Emission exprLowering emitHelper freshWrites compileEnv venomInst
  exprLoweringProps exprOperandVar

Theorem extract32_emit_op_excluded_register:
  not_fresh_at sa v /\ EVERY (\a. a <> Var v) args /\
  emit_op opc args sa = (r,sb) ==>
  r <> Var v /\
  ?delta.
    FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
    (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ delta /\
    EVERY (\i. ~MEM v i.inst_outputs /\ ~MEM (Var v) i.inst_operands) delta
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  rpt gen_tac >> disch_tac >>
  gvs[mk_inst_def, listTheory.APPEND_ASSOC, listTheory.EVERY_MEM,
      not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem extract32_emit_void_excluded_register:
  EVERY (\a. a <> Var v) args /\ emit_void opc args sa = (r,sb) ==>
  ?delta.
    FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
    (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ delta /\
    EVERY (\i. ~MEM v i.inst_outputs /\ ~MEM (Var v) i.inst_operands) delta
Proof
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def] >>
  rpt strip_tac >>
  gvs[mk_inst_def, listTheory.APPEND_ASSOC, listTheory.EVERY_MEM]
QED


Theorem extract32_emit_inst_excluded_register:
  EVERY (\a. a <> Var v) args /\ ~MEM v outs /\
  emit_inst opc args outs sa = (u,sb) ==>
  ?delta.
    FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
    (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ delta /\
    EVERY (\i. ~MEM v i.inst_outputs /\ ~MEM (Var v) i.inst_operands) delta
Proof
  simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def] >> rpt strip_tac >>
  gvs[mk_inst_def, listTheory.APPEND_ASSOC, listTheory.EVERY_MEM]
QED

Theorem extract32_fresh_var_chronological:
  fresh_var sa = (r,sb) ==>
  FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
  FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts
Proof
  simp[fresh_var_def] >> rpt strip_tac >> gvs[]
QED

Theorem extract32_fresh_var_excluded_register:
  fresh_var sa = (r,sb) /\ not_fresh_at sa v ==> r <> v
Proof
  simp[fresh_var_def] >> rpt strip_tac >> gvs[not_fresh_at_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem extract32_fresh_label_chronological:
  fresh_label prefix sa = (r,sb) ==>
  FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
  FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts
Proof
  simp[fresh_label_def] >> rpt strip_tac >> gvs[]
QED

Theorem extract32_imm_load_word_excluded_register:
  not_fresh_at sa v /\ off <> Var v /\
  (!base. imm = SOME base ==> base <> Var v) /\
  compile_imm_load_word is_ctor imm off sa = (r,sb) ==>
  r <> Var v /\
  ?delta.
    FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
    (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ delta /\
    EVERY (\i. ~MEM v i.inst_outputs /\ ~MEM (Var v) i.inst_operands) delta
Proof
  Cases_on `is_ctor` >> Cases_on `imm` >>
  simp[contextTheory.compile_imm_load_word_def, emit_op_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  rpt gen_tac >> disch_tac >>
  gvs[mk_inst_def, listTheory.APPEND_ASSOC, listTheory.EVERY_MEM,
      not_fresh_at_def] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.LESS_EQ_ADD]
QED

Theorem extract32_imm_load_word_result_excluded:
  not_fresh_at sa v /\ off <> Var v /\
  (!base. imm = SOME base ==> base <> Var v) /\
  compile_imm_load_word is_ctor imm off sa = (r,sb) ==> r <> Var v
Proof
  metis_tac[extract32_imm_load_word_excluded_register]
QED

Theorem extract32_imm_load_word_delta_excluded:
  not_fresh_at sa v /\ off <> Var v /\
  (!base. imm = SOME base ==> base <> Var v) /\
  compile_imm_load_word is_ctor imm off sa = (r,sb) ==>
  ?delta.
    FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
    (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ delta /\
    EVERY (\i. ~MEM v i.inst_outputs /\ ~MEM (Var v) i.inst_operands) delta
Proof
  metis_tac[extract32_imm_load_word_excluded_register]
QED

Theorem extract32_ptr_load_result_excluded:
  not_fresh_at sa v /\ off <> Var v /\
  (!base. imm = SOME base ==> base <> Var v) /\
  compile_ptr_load is_ctor imm loc off sa = (r,sb) ==> r <> Var v
Proof
  Cases_on `loc` >> simp[contextTheory.compile_ptr_load_def] >> rpt strip_tac >>
  FIRST [drule_at (Pos last) extract32_emit_op_excluded_register,
         drule_at (Pos last) extract32_imm_load_word_result_excluded] >>
  disch_then (qspec_then `v` mp_tac) >> simp[]
QED

Theorem extract32_ptr_load_delta_excluded:
  not_fresh_at sa v /\ off <> Var v /\
  (!base. imm = SOME base ==> base <> Var v) /\
  compile_ptr_load is_ctor imm loc off sa = (r,sb) ==>
  ?delta.
    FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
    (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ delta /\
    EVERY (\i. ~MEM v i.inst_outputs /\ ~MEM (Var v) i.inst_operands) delta
Proof
  Cases_on `loc` >> simp[contextTheory.compile_ptr_load_def] >> rpt strip_tac >>
  FIRST [drule_at (Pos last) extract32_emit_op_excluded_register,
         drule_at (Pos last) extract32_imm_load_word_delta_excluded] >>
  disch_then (qspec_then `v` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem extract32_ptr_store_none_delta_excluded:
  dst <> Var v /\ value <> Var v /\
  compile_ptr_store is_ctor NONE loc dst value sa = (r,sb) ==>
  ?delta.
    FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
    (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ delta /\
    EVERY (\i. ~MEM v i.inst_outputs /\ ~MEM (Var v) i.inst_operands) delta
Proof
  Cases_on `loc` >> Cases_on `is_ctor` >>
  simp[contextTheory.compile_ptr_store_def, contextTheory.compile_imm_store_word_def] >>
  rpt strip_tac >> drule_at (Pos last) extract32_emit_void_excluded_register >>
  disch_then (qspec_then `v` mp_tac) >> simp[]
QED

Theorem extract32_alloc_buffer_result_excluded:
  not_fresh_at sa v /\ compile_alloc_buffer nbytes sa = (r,sb) ==>
  r.buf_operand <> Var v
Proof
  simp[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> rpt strip_tac >> gvs[] >>
  drule_at (Pos last) extract32_emit_op_excluded_register >>
  disch_then (qspec_then `v` mp_tac) >> simp[]
QED

Theorem extract32_alloc_buffer_delta_excluded:
  not_fresh_at sa v /\ compile_alloc_buffer nbytes sa = (r,sb) ==>
  ?delta.
    FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
    (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ delta /\
    EVERY (\i. ~MEM v i.inst_outputs /\ ~MEM (Var v) i.inst_operands) delta
Proof
  simp[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> rpt strip_tac >> gvs[] >>
  drule_at (Pos last) extract32_emit_op_excluded_register >>
  disch_then (qspec_then `v` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem extract32_lit_byte_offset_result_excluded:
  not_fresh_at sa v /\ op <> Var v /\
  compile_lit_byte_offset op off sa = (r,sb) ==> r <> Var v
Proof
  Cases_on `off = 0` >> simp[contextTheory.compile_lit_byte_offset_def, comp_return_def] >>
  Cases_on `op` >> simp[comp_return_def] >> rpt strip_tac >> gvs[] >>
  drule_at (Pos last) extract32_emit_op_excluded_register >>
  disch_then (qspec_then `v` mp_tac) >> simp[]
QED

Theorem extract32_lit_byte_offset_delta_excluded:
  not_fresh_at sa v /\ op <> Var v /\
  compile_lit_byte_offset op off sa = (r,sb) ==>
  ?delta.
    FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
    (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ delta /\
    EVERY (\i. ~MEM v i.inst_outputs /\ ~MEM (Var v) i.inst_operands) delta
Proof
  Cases_on `off = 0` >> simp[contextTheory.compile_lit_byte_offset_def, comp_return_def] >>
  Cases_on `op` >> simp[comp_return_def] >> rpt strip_tac >> gvs[] >>
  FIRST [qexists_tac `[]` >> simp[] >> NO_TAC,
         drule_at (Pos last) extract32_emit_op_excluded_register >>
         disch_then (qspec_then `v` mp_tac) >> simp[] >> metis_tac[]]
QED

(* Normalize a successful compiler call against a ci_mono schema once.
   This is proof support only; all facts are reconstructed by kernel rules. *)
fun extract32_call_mono_tac eq =
  MAP_FIRST (fn mono => fn goal =>
    let val inst = PART_MATCH (rand o rand) mono (lhs (concl eq))
    in assume_tac (REWRITE_RULE [eq, pairTheory.SND] inst) goal end)
    [ci_mono_fresh_label, ci_mono_fresh_var, ci_mono_new_block,
     ci_mono_emit_op, ci_mono_emit_inst, ci_mono_emit_void,
     ci_mono_compile_ptr_load];

(* Apply a matched call boundary only once its side conditions simplify.
   Remove consumed equations so a repeated pass cannot duplicate suffixes. *)
fun extract32_call_delta_tac eq =
  MAP_FIRST (fn boundary => fn goal =>
    (mp_then (Pos last) (qspec_then `v` mp_tac) boundary eq >>
     (impl_tac >- (simp[] >> NO_TAC)) >> strip_tac >>
     WEAKEN_TAC (aconv (concl eq))) goal)
    [extract32_emit_op_excluded_register, extract32_emit_inst_excluded_register,
     extract32_emit_void_excluded_register, extract32_ptr_load_delta_excluded];

Theorem extract32_word_copy_loop_delta_excluded:
  not_fresh_at sa v /\ src <> Var v /\ dst <> Var v /\
  compile_word_copy_loop src dst wc ll sl ic sa = (u,sb) ==>
  ?delta.
    FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
    (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ delta /\
    EVERY (\i. ~MEM v i.inst_outputs /\ ~MEM (Var v) i.inst_operands) delta
Proof
  simp[contextTheory.compile_word_copy_loop_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> rpt strip_tac >>
  Cases_on `sl` >> Cases_on `ic` >>
  gvs[contextTheory.compile_ptr_store_def, contextTheory.compile_imm_store_word_def,
      word_scale_def, comp_bind_def] >>
  Cases_on `word_scale ll = 1` >> gvs[comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  every_assum (fn eq => TRY (extract32_call_mono_tac eq)) >>
  ntac 2 (imp_res_tac compiler_ci_mono_not_fresh) >>
  qpat_assum `fresh_var _ = _`
    (mp_then (Pos hd) (qspec_then `v` mp_tac) extract32_fresh_var_excluded_register) >>
  simp[] >> strip_tac >>
  rpt (CHANGED_TAC (
    every_assum (fn eq => TRY (
      mp_then (Pos last) (qspec_then `v` mp_tac) extract32_ptr_load_result_excluded eq >>
      (impl_tac >- (simp[] >> NO_TAC)) >> strip_tac)) >>
    every_assum (fn eq => TRY (extract32_call_delta_tac eq)))) >>
  imp_res_tac extract32_fresh_label_chronological >>
  imp_res_tac extract32_fresh_var_chronological >>
  imp_res_tac extract32_new_block_chronological >>
  simp[listTheory.APPEND_ASSOC, listTheory.EVERY_APPEND]
QED

Theorem extract32_storage_to_memory_delta_excluded:
  not_fresh_at sa v /\ src <> Var v /\ dst <> Var v /\
  compile_storage_to_memory src dst wc sa = (u,sb) ==>
  ?delta.
    FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
    (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ delta /\
    EVERY (\i. ~MEM v i.inst_outputs /\ ~MEM (Var v) i.inst_operands) delta
Proof
  simp[contextTheory.compile_storage_to_memory_def] >>
  metis_tac[extract32_word_copy_loop_delta_excluded]
QED

Theorem extract32_transient_to_memory_delta_excluded:
  not_fresh_at sa v /\ src <> Var v /\ dst <> Var v /\
  compile_transient_to_memory src dst wc sa = (u,sb) ==>
  ?delta.
    FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
    (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ delta /\
    EVERY (\i. ~MEM v i.inst_outputs /\ ~MEM (Var v) i.inst_operands) delta
Proof
  simp[contextTheory.compile_transient_to_memory_def] >>
  metis_tac[extract32_word_copy_loop_delta_excluded]
QED

Theorem extract32_imm_copy_to_memory_delta_excluded:
  !n sa off sb u ic imm src dst v.
  not_fresh_at sa v /\ src <> Var v /\ dst <> Var v /\
  (!base. imm = SOME base ==> base <> Var v) /\
  compile_imm_copy_to_memory ic imm src dst n off sa = (u,sb) ==>
  ?delta.
    FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
    (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ delta /\
    EVERY (\i. ~MEM v i.inst_outputs /\ ~MEM (Var v) i.inst_operands) delta
Proof
  Induct
  >- (simp[contextTheory.compile_imm_copy_to_memory_def, comp_return_def] >>
      rpt strip_tac >> gvs[]) >>
  simp[Once contextTheory.compile_imm_copy_to_memory_def, comp_bind_def,
       comp_ignore_bind_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> simp[]) >> rpt strip_tac >>
  Cases_on `off = 0` >> Cases_on `src` >> Cases_on `dst` >>
  Cases_on `ic` >> Cases_on `imm` >>
  gvs[contextTheory.compile_lit_byte_offset_def, contextTheory.compile_imm_load_word_def,
      comp_return_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  every_assum (fn eq => TRY (extract32_call_mono_tac eq)) >>
  ntac 2 (imp_res_tac compiler_ci_mono_not_fresh) >>
  rpt (CHANGED_TAC (every_assum (fn eq => TRY (extract32_call_delta_tac eq)))) >>
  qpat_x_assum `!sa off sb ic imm src dst v. _` (drule_at (Pos last)) >>
  disch_then (qspec_then `v` mp_tac) >> simp[] >> strip_tac >>
  simp[listTheory.APPEND_ASSOC, listTheory.EVERY_APPEND]
QED
