(* Immutable writes share physical MSTORE effects, with masked bookkeeping. *)
Theory lowerDloadSafetyImmutableWriteEffects
Ancestors
  lowerDloadSafetyMemoryWriteEffects lowerDloadSafetyRelation
  lowerDloadSafetyKernel ptrDiscipline venomExecSemantics venomInst
  venomState memLocDefs codegenRel finite_map pred_set list words arithmetic

Theorem ld_istore_step[local]:
  inst.inst_opcode = ISTORE /\ inst.inst_operands = [a;v] /\
  eval_operand a s = SOME dst /\ eval_operand v s = SOME x ==>
  step_inst_base inst s = OK (istore (w2n dst) x s)
Proof
  strip_tac >> pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[exec_write2_def, eval_operands_def]
QED

Theorem ld_istore_taint[local]:
  inst.inst_opcode = ISTORE /\ inst.inst_operands = [a;v] /\
  inst.inst_outputs = [] /\ eval_operand a s = SOME dst /\
  eval_operand v s = SOME x /\ op_taint tn v SUBSET {j | j < 32} ==>
  step_taint inst s (istore (w2n dst) x s) tn =
    tn with <| t_mem := (tn.t_mem DIFF {w2n dst+j | j < 32}) UNION
                          {w2n dst+j | j < 32 /\ j IN op_taint tn v};
               t_imm := key_update tn.t_imm (w2n dst) (op_taint tn v) |>
Proof
  strip_tac >>
  `{i | w2n dst <= i /\ i < w2n dst+32} = {w2n dst+j | j < 32}` by
    (simp[EXTENSION] >> qx_gen_tac `i` >> eq_tac
     >- (strip_tac >> qexists_tac `i-w2n dst` >> decide_tac) >>
     strip_tac >> gvs[] >> decide_tac) >>
  simp[step_taint_def, mem_taint_def, written_taint_def, step_writes_def,
       new_site_bytes_def, source_memory_write_ranges_def, range_bytes_def,
       istore_def, mstore_def, set_var_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, taint_component_equality,
       FLOOKUP_DEF, DRESTRICT_UNIV, fixed_source_write_range_def] >>
  gvs[SUBSET_DEF, EXTENSION] >> metis_tac[]
QED

Theorem ld_memory_istore_bookkeeping[local]:
  ld_memory lo A tn (mstore d x s) (mstore d y t) ==>
  ld_memory lo A tn (istore d x s) (istore d y t)
Proof
  simp[ld_memory_def, istore_def] >> metis_tac[]
QED

Theorem ld_nonghost_istore:
  ld_nonghost tn s t /\ word_agree_except M x y ==>
  ld_nonghost (tn with <|t_mem := X;
    t_imm := key_update tn.t_imm d M|>) (istore d x s) (istore d y t)
Proof
  simp[ld_nonghost_def, istore_def, mstore_def, FLOOKUP_UPDATE] >>
  strip_tac >> rpt conj_tac >> rpt gen_tac >>
  Cases_on `k = d` >> gvs[key_taint_def, key_update_def, word_agree_except_def] >>
  metis_tac[]
QED

Theorem ld_istore_effect:
  ld_vars P A f /\ tn.t_var = f.lf_tv /\
  inst.inst_opcode = ISTORE /\ inst.inst_operands = [a;v] /\
  inst.inst_outputs = [] /\
  eval_operand a f.lf_src = SOME dst /\
  eval_operand a f.lf_tgt = SOME dst /\
  eval_operand v f.lf_src = SOME x /\
  eval_operand v f.lf_tgt = SOME y /\
  word_agree_except (op_taint tn v) x y /\
  op_taint tn v SUBSET {j | j < 32} /\
  ld_global lo A frames /\ FDOM A = ld_slots A frames /\
  EVERY (ld_maps A) frames /\
  (w2n dst+32 <= lo \/
   (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
     w2n dst=b+delta /\ w2n dst=c+delta /\ delta+32 <= sz)) /\
  step_inst_base inst f.lf_tgt = OK ts /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\ ld_nonghost tn f.lf_src f.lf_tgt ==>
  ?ss. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <| lf_src := ss; lf_tgt := ts;
      lf_tv := (step_taint inst f.lf_src ss tn).t_var |> ) /\
    ld_memory lo A (step_taint inst f.lf_src ss tn) ss ts /\
    ld_nonghost (step_taint inst f.lf_src ss tn) ss ts /\
    step_prov (MAP (OPTION_MAP (ld_erase A)) f.lf_Q)
      (ld_erase A o_f f.lf_H) inst ss = ld_erase A o_f f.lf_H /\
    ss.vs_allocas = f.lf_src.vs_allocas /\
    ss.vs_alloca_next = f.lf_src.vs_alloca_next /\
    ss.vs_params = f.lf_src.vs_params /\
    ss.vs_current_bb = f.lf_src.vs_current_bb /\
    ss.vs_prev_bb = f.lf_src.vs_prev_bb /\
    ss.vs_inst_idx = f.lf_src.vs_inst_idx /\
    ss.vs_labels = f.lf_src.vs_labels /\
    ss.vs_return_pc_token = f.lf_src.vs_return_pc_token /\
    ts.vs_allocas = f.lf_tgt.vs_allocas /\
    ts.vs_alloca_next = f.lf_tgt.vs_alloca_next /\
    ts.vs_params = f.lf_tgt.vs_params /\
    ts.vs_current_bb = f.lf_tgt.vs_current_bb /\
    ts.vs_prev_bb = f.lf_tgt.vs_prev_bb /\
    ts.vs_inst_idx = f.lf_tgt.vs_inst_idx /\
    ts.vs_labels = f.lf_tgt.vs_labels /\
    ts.vs_return_pc_token = f.lf_tgt.vs_return_pc_token
Proof
  strip_tac >>
  `step_inst_base inst f.lf_src = OK (istore (w2n dst) x f.lf_src)` by
    (irule ld_istore_step >> simp[]) >>
  `step_inst_base inst f.lf_tgt = OK (istore (w2n dst) y f.lf_tgt)` by
    (irule ld_istore_step >> simp[]) >>
  `step_taint inst f.lf_src (istore (w2n dst) x f.lf_src) tn =
     tn with <|t_mem := (tn.t_mem DIFF {w2n dst+j | j < 32}) UNION
                          {w2n dst+j | j < 32 /\ j IN op_taint tn v};
               t_imm := key_update tn.t_imm (w2n dst) (op_taint tn v)|>` by
    (irule ld_istore_taint >> simp[]) >>
  qexists_tac `istore (w2n dst) x f.lf_src` >> gvs[] >>
  (conj_tac >- gvs[ld_vars_def, istore_def, mstore_def] >>
   conj_tac >- (
     irule ld_memory_istore_bookkeeping >>
     irule ld_memory_mstore >>
     conj_tac >- metis_tac[] >>
     conj_tac >- (qexists_tac `frames` >> simp[]) >>
     qexistsl_tac [`op_taint tn v`, `tn`] >>
     simp[AC ADD_ASSOC ADD_COMM]) >>
   conj_tac >- (irule ld_nonghost_istore >> simp[]) >>
   simp[step_prov_def, set_prov_def, DRESTRICT_UNIV, istore_def, mstore_def])
QED
