(* Masked memory-word writes at classified physical addresses. *)
Theory lowerDloadSafetyMemoryWriteEffects
Ancestors
  lowerDloadSafetyWriteBytes lowerDloadSafetyAllocBounds
  lowerDloadSafetyRelation lowerDloadSafetyKernel ptrDiscipline venomExecSemantics venomInst
  venomState memLocDefs codegenRel finite_map pred_set list byte words arithmetic

Theorem ld_mstore_as_write[local]:
  mstore off x s = write_memory_with_expansion off (word_to_bytes x T) s
Proof
  simp[mstore_def, write_memory_with_expansion_def, LENGTH_word_to_bytes,
       fcpLib.INDEX_CONV ``dimindex(:256)``]
QED

Theorem ld_mstore_step[local]:
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [a;v] /\
  eval_operand a s = SOME dst /\ eval_operand v s = SOME x ==>
  step_inst_base inst s = OK (mstore (w2n dst) x s)
Proof
  strip_tac >> pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[exec_write2_def, eval_operands_def]
QED

Theorem ld_mstore_taint[local]:
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [a;v] /\
  inst.inst_outputs = [] /\ eval_operand a s = SOME dst /\
  eval_operand v s = SOME x /\ op_taint tn v SUBSET {j | j < 32} ==>
  step_taint inst s (mstore (w2n dst) x s) tn =
    tn with t_mem := (tn.t_mem DIFF {w2n dst+j | j < 32}) UNION
                          {w2n dst+j | j < 32 /\ j IN op_taint tn v}
Proof
  strip_tac >>
  `{i | w2n dst <= i /\ i < w2n dst+32} = {w2n dst+j | j < 32}` by
    (simp[EXTENSION] >> qx_gen_tac `i` >> eq_tac
     >- (strip_tac >> qexists_tac `i-w2n dst` >> decide_tac) >>
     strip_tac >> gvs[] >> decide_tac) >>
  simp[step_taint_def, mem_taint_def, written_taint_def, step_writes_def,
       new_site_bytes_def, source_memory_write_ranges_def, range_bytes_def,
       mstore_def, set_var_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, taint_component_equality,
       FLOOKUP_DEF, DRESTRICT_UNIV, fixed_source_write_range_def] >>
  gvs[SUBSET_DEF, EXTENSION] >> metis_tac[]
QED

(* Shared physical word-write boundary; immutable bookkeeping is independent. *)
Theorem ld_memory_mstore:
  word_agree_except M x y /\ M SUBSET {j | j < 32} /\
  ld_global lo A frames /\ FDOM A = ld_slots A frames /\
  EVERY (ld_maps A) frames /\
  ((d+32 <= lo /\ d'=d) \/
   (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
     d=b+delta /\ d'=c+delta /\ delta+32 <= sz)) /\
  ld_memory lo A tn s t /\
  tn'.t_mem = (tn.t_mem DIFF {d+j | j < 32}) UNION
      {d+j | j < 32 /\ j IN M} ==>
  ld_memory lo A tn' (mstore d x s) (mstore d' y t)
Proof
  strip_tac >>
  `ld_memory lo A
    (tn with t_mem := (tn.t_mem DIFF {d+j | j < 32}) UNION
      {d+j | j < 32 /\ j IN M})
    (mstore d x s) (mstore d' y t)` suffices_by
    gvs[ld_memory_def] >>
  gvs[] >> rewrite_tac[ld_mstore_as_write]
  >- (irule ld_memory_write_low >>
      simp[LENGTH_word_to_bytes, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
      conj_tac >- metis_tac[ld_alloc_bounds] >>
      qexistsl_tac [`M`, `tn`] >> gvs[word_agree_except_def]) >>
  irule ld_memory_write_slot >>
  simp[LENGTH_word_to_bytes, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  conj_tac >- metis_tac[ld_alloc_bounds] >>
  qexistsl_tac [`M`, `k`, `sz`, `tn`] >>
  gvs[word_agree_except_def] >> rpt strip_tac >>
  `0 < sz` by decide_tac >> metis_tac[ld_alloc_separate]
QED

Theorem ld_mstore_effect:
  ld_vars P A f /\ tn.t_var = f.lf_tv /\
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [a;v] /\
  inst.inst_outputs = [] /\
  eval_operand a f.lf_src = SOME dst /\
  eval_operand a f.lf_tgt = SOME dst' /\
  eval_operand v f.lf_src = SOME x /\
  eval_operand v f.lf_tgt = SOME y /\
  word_agree_except (op_taint tn v) x y /\
  op_taint tn v SUBSET {j | j < 32} /\
  ld_global lo A frames /\ FDOM A = ld_slots A frames /\
  EVERY (ld_maps A) frames /\
  ld_dyn_agree fl tn.t_mem f.lf_src.vs_memory f.lf_tgt.vs_memory /\
  lo <= fl /\
  (!a u v z. FLOOKUP A a = SOME (u,v,z) ==> u+z <= fl /\ v+z <= fl) /\
  ((w2n dst+32 <= lo /\ dst'=dst) \/
   (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
     w2n dst=b+delta /\ w2n dst'=c+delta /\ delta+32 <= sz) \/
   (dst'=dst /\ fl <= w2n dst)) /\
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
  `step_inst_base inst f.lf_src = OK (mstore (w2n dst) x f.lf_src)` by
    (irule ld_mstore_step >> simp[]) >>
  `step_inst_base inst f.lf_tgt = OK (mstore (w2n dst') y f.lf_tgt)` by
    (irule ld_mstore_step >> simp[]) >>
  `step_taint inst f.lf_src (mstore (w2n dst) x f.lf_src) tn =
     tn with t_mem := (tn.t_mem DIFF {w2n dst+j | j < 32}) UNION
                          {w2n dst+j | j < 32 /\ j IN op_taint tn v}` by
    (irule ld_mstore_taint >> simp[]) >>
  `ld_memory lo A
     (tn with t_mem := (tn.t_mem DIFF {w2n dst+j | j < 32}) UNION
                          {w2n dst+j | j < 32 /\ j IN op_taint tn v})
     (mstore (w2n dst) x f.lf_src) (mstore (w2n dst') y f.lf_tgt)` by
    (Cases_on `dst' = dst /\ fl <= w2n dst`
     >- (pop_assum strip_assume_tac >>
         qpat_x_assum `dst' = dst` SUBST_ALL_TAC >>
         rewrite_tac[ld_mstore_as_write] >>
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
  `ld_dyn_agree fl
     ((tn.t_mem DIFF {w2n dst+j | j < 32}) UNION
       {w2n dst+j | j < 32 /\ j IN op_taint tn v})
     (mstore (w2n dst) x f.lf_src).vs_memory
     (mstore (w2n dst') y f.lf_tgt).vs_memory` by
    (qpat_x_assum `_ \/ _ \/ _` strip_assume_tac >>
     rewrite_tac[ld_mstore_as_write] >> irule ld_dyn_agree_write >>
     qexistsl_tac [`op_taint tn v`, `32`, `tn`] >>
     simp[LENGTH_word_to_bytes, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
     FIRST [fs[word_agree_except_def] >> NO_TAC,
            res_tac >> rpt disj2_tac >> decide_tac]) >>
  qexists_tac `mstore (w2n dst) x f.lf_src` >> gvs[] >>
  rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC,
         gvs[ld_vars_def, mstore_def] >> NO_TAC,
         gvs[ld_nonghost_def, mstore_def] >> NO_TAC,
         simp[step_prov_def, set_prov_def, DRESTRICT_UNIV, mstore_def]]
QED

Theorem ld_mstore8_as_write[local]:
  mstore8 off x s = write_memory_with_expansion off [(w2w x : word8)] s
Proof
  simp[mstore8_def, write_memory_with_expansion_def]
QED

Theorem ld_mstore8_step[local]:
  inst.inst_opcode = MSTORE8 /\ inst.inst_operands = [a;v] /\
  eval_operand a s = SOME dst /\ eval_operand v s = SOME x ==>
  step_inst_base inst s = OK (mstore8 (w2n dst) x s)
Proof
  strip_tac >> pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[exec_write2_def, eval_operands_def]
QED

Theorem ld_mstore8_taint[local]:
  inst.inst_opcode = MSTORE8 /\ inst.inst_operands = [a;v] /\
  inst.inst_outputs = [] /\ eval_operand a s = SOME dst /\
  eval_operand v s = SOME x ==>
  step_taint inst s (mstore8 (w2n dst) x s) tn =
    tn with t_mem := tn.t_mem DIFF {w2n dst}
Proof
  strip_tac >>
  simp[step_taint_def, mem_taint_def, written_taint_def, step_writes_def,
       new_site_bytes_def, source_memory_write_ranges_def, range_bytes_def,
       mstore8_def, set_var_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, taint_component_equality,
       FLOOKUP_DEF, DRESTRICT_UNIV, fixed_source_write_range_def] >>
  gvs[EXTENSION] >> qx_gen_tac `i` >>
  `w2n dst <= i /\ i < w2n dst+1 <=> i = w2n dst` by decide_tac >>
  metis_tac[]
QED

Theorem ld_mstore8_effect:
  ld_vars P A f /\ tn.t_var = f.lf_tv /\
  inst.inst_opcode = MSTORE8 /\ inst.inst_operands = [a;v] /\
  inst.inst_outputs = [] /\
  eval_operand a f.lf_src = SOME dst /\
  eval_operand a f.lf_tgt = SOME dst' /\
  eval_operand v f.lf_src = SOME x /\
  eval_operand v f.lf_tgt = SOME y /\
  (w2w x : word8) = w2w y /\
  ld_global lo A frames /\ FDOM A = ld_slots A frames /\
  EVERY (ld_maps A) frames /\
  ld_dyn_agree fl tn.t_mem f.lf_src.vs_memory f.lf_tgt.vs_memory /\
  lo <= fl /\
  (!a u v z. FLOOKUP A a = SOME (u,v,z) ==> u+z <= fl /\ v+z <= fl) /\
  ((w2n dst+1 <= lo /\ dst'=dst) \/
   (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
     w2n dst=b+delta /\ w2n dst'=c+delta /\ delta+1 <= sz) \/
   (dst'=dst /\ fl <= w2n dst)) /\
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
  `step_inst_base inst f.lf_src = OK (mstore8 (w2n dst) x f.lf_src)` by
    (irule ld_mstore8_step >> simp[]) >>
  `step_inst_base inst f.lf_tgt = OK (mstore8 (w2n dst') y f.lf_tgt)` by
    (irule ld_mstore8_step >> simp[]) >>
  `step_taint inst f.lf_src (mstore8 (w2n dst) x f.lf_src) tn =
     tn with t_mem := tn.t_mem DIFF {w2n dst}` by
    (irule ld_mstore8_taint >> simp[]) >>
  `tn.t_mem DIFF {w2n dst} =
   (tn.t_mem DIFF {w2n dst + j | j < 1}) UNION {w2n dst + j | j < 1 /\ j IN {}}`
    by simp[EXTENSION] >>
  `ld_memory lo A (tn with t_mem := tn.t_mem DIFF {w2n dst})
     (mstore8 (w2n dst) x f.lf_src) (mstore8 (w2n dst') y f.lf_tgt)` by
    (rewrite_tac[ld_mstore8_as_write] >>
     Cases_on `dst' = dst /\ fl <= w2n dst`
     >- (pop_assum strip_assume_tac >>
         qpat_x_assum `dst' = dst` SUBST_ALL_TAC >>
         qpat_assum `tn.t_mem DIFF _ = _` (fn th => rewrite_tac[th]) >>
         irule ld_memory_write_high >> rpt conj_tac >>
         FIRST [qexistsl_tac [`{}`, `1`, `tn`] >> simp[EXTENSION] >> NO_TAC,
                decide_tac,
                rpt strip_tac >> res_tac >> decide_tac]) >>
     `(w2n dst+1 <= lo /\ dst'=dst) \/
      (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
        w2n dst=b+delta /\ w2n dst'=c+delta /\ delta+1 <= sz)` by metis_tac[] >>
     qpat_x_assum `_ \/ _ \/ _` kall_tac >>
     pop_assum strip_assume_tac
     >- (qpat_x_assum `dst' = dst` SUBST_ALL_TAC >>
         irule ld_memory_write_low >>
         conj_tac >- metis_tac[ld_alloc_bounds] >>
         qexistsl_tac [`{}`, `1`, `tn`] >> simp[EXTENSION]) >>
     qpat_x_assum `w2n dst = _` (fn th => rewrite_tac[th]) >>
     qpat_x_assum `w2n dst' = _` (fn th => rewrite_tac[th]) >>
     irule ld_memory_write_slot >>
     conj_tac >- metis_tac[ld_alloc_bounds] >>
     qexistsl_tac [`{}`, `k`, `1`, `sz`, `tn`] >>
     simp[EXTENSION] >> rpt strip_tac >>
     `0 < sz` by decide_tac >> metis_tac[ld_alloc_separate]) >>
  `ld_dyn_agree fl (tn.t_mem DIFF {w2n dst})
     (mstore8 (w2n dst) x f.lf_src).vs_memory
     (mstore8 (w2n dst') y f.lf_tgt).vs_memory` by
    (qpat_x_assum `_ \/ _ \/ _` strip_assume_tac >>
     qpat_assum `tn.t_mem DIFF _ = _` (fn th => rewrite_tac[th]) >>
     rewrite_tac[ld_mstore8_as_write] >> irule ld_dyn_agree_write >>
     qexistsl_tac [`{}`, `1`, `tn`] >> simp[] >>
     FIRST [fs[] >> NO_TAC,
            res_tac >> rpt disj2_tac >> decide_tac]) >>
  qexists_tac `mstore8 (w2n dst) x f.lf_src` >> gvs[] >>
  rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC,
         gvs[ld_vars_def, mstore8_def] >> NO_TAC,
         gvs[ld_nonghost_def, mstore8_def] >> NO_TAC,
         simp[step_prov_def, set_prov_def, DRESTRICT_UNIV, mstore8_def]]
QED
