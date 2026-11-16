(* Immutable writes share physical MSTORE effects, with masked bookkeeping. *)
Theory lowerDloadSafetyImmutableWriteEffects
Ancestors
  lowerDloadSafetyMemoryWriteEffects lowerDloadSafetyWriteBytes lowerDloadSafetyRelation byte
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
  ld_dyn_agree fl tn.t_mem f.lf_src.vs_memory f.lf_tgt.vs_memory /\
  lo <= fl /\
  (!a u v z. FLOOKUP A a = SOME (u,v,z) ==> u+z <= fl /\ v+z <= fl) /\
  (w2n dst+32 <= lo \/
   (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
     w2n dst=b+delta /\ w2n dst=c+delta /\ delta+32 <= sz) \/
   fl <= w2n dst) /\
  step_inst_base inst f.lf_tgt = OK ts /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\ ld_nonghost tn f.lf_src f.lf_tgt ==>
  ?ss. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <| lf_src := ss; lf_tgt := ts;
      lf_tv := (step_taint inst f.lf_src ss tn).t_var |> ) /\
    ld_memory lo A (step_taint inst f.lf_src ss tn) ss ts /\
    ld_nonghost (step_taint inst f.lf_src ss tn) ss ts /\
    ld_dyn_agree fl (step_taint inst f.lf_src ss tn).t_mem
      ss.vs_memory ts.vs_memory /\
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
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `step_inst_base inst f.lf_src = OK (istore (w2n dst) x f.lf_src)` by
    (irule ld_istore_step >> simp[]) >>
  `step_inst_base inst f.lf_tgt = OK (istore (w2n dst) y f.lf_tgt)` by
    (irule ld_istore_step >> simp[]) >>
  `step_taint inst f.lf_src (istore (w2n dst) x f.lf_src) tn =
     tn with <|t_mem := (tn.t_mem DIFF {w2n dst+j | j < 32}) UNION
                          {w2n dst+j | j < 32 /\ j IN op_taint tn v};
               t_imm := key_update tn.t_imm (w2n dst) (op_taint tn v)|>` by
    (irule ld_istore_taint >> simp[]) >>
  `!z w. mstore (w2n dst) w z =
         write_memory_with_expansion (w2n dst) (word_to_bytes w T) z` by
    simp[mstore_def, write_memory_with_expansion_def, LENGTH_word_to_bytes,
         fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  `!z w. (istore (w2n dst) w z).vs_memory = (mstore (w2n dst) w z).vs_memory`
    by simp[istore_def] >>
  `ld_dyn_agree fl
     ((tn.t_mem DIFF {w2n dst+j | j < 32}) UNION
       {w2n dst+j | j < 32 /\ j IN op_taint tn v})
     (istore (w2n dst) x f.lf_src).vs_memory
     (istore (w2n dst) y f.lf_tgt).vs_memory` by
    (qpat_assum `!z w. (istore _ _ _).vs_memory = _`
       (fn th => rewrite_tac[th]) >>
     qpat_assum `!z w. mstore _ _ _ = _` (fn th => rewrite_tac[th]) >>
     irule ld_dyn_agree_write >>
     qexistsl_tac [`op_taint tn v`, `32`, `tn`] >>
     rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
            disj2_tac >> disj1_tac >> fs[word_agree_except_def] >> NO_TAC,
            simp[LENGTH_word_to_bytes, fcpLib.INDEX_CONV ``dimindex(:256)``]]) >>
  `ld_memory lo A
     (tn with <|t_mem := (tn.t_mem DIFF {w2n dst+j | j < 32}) UNION
                          {w2n dst+j | j < 32 /\ j IN op_taint tn v};
               t_imm := key_update tn.t_imm (w2n dst) (op_taint tn v)|>)
     (istore (w2n dst) x f.lf_src) (istore (w2n dst) y f.lf_tgt)` by
    (irule ld_memory_istore_bookkeeping >>
     Cases_on `fl <= w2n dst`
     >- (qpat_assum `!z w. mstore _ _ _ = _` (fn th => rewrite_tac[th]) >>
         irule ld_memory_write_high >> rpt conj_tac >>
         FIRST [qexistsl_tac [`op_taint tn v`, `32`, `tn`] >>
                simp[LENGTH_word_to_bytes, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
                NO_TAC,
                decide_tac,
                rpt strip_tac >> res_tac >> decide_tac]) >>
     irule ld_memory_mstore >>
     conj_tac >- metis_tac[] >>
     conj_tac >- (qexists_tac `frames` >> simp[]) >>
     qexistsl_tac [`op_taint tn v`, `tn`] >>
     simp[AC ADD_ASSOC ADD_COMM]) >>
  qpat_x_assum `!z w. (istore _ _ _).vs_memory = _` kall_tac >>
  qpat_x_assum `!z w. mstore _ _ _ = _` kall_tac >>
  qexists_tac `istore (w2n dst) x f.lf_src` >> gvs[] >>
  rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC,
         gvs[ld_vars_def, istore_def, mstore_def] >> NO_TAC,
         irule ld_nonghost_istore >> simp[] >> NO_TAC,
         simp[step_prov_def, set_prov_def, DRESTRICT_UNIV, istore_def, mstore_def]]
QED
