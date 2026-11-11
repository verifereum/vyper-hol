(* Reachable memory-write consumers. *)
Theory lowerDloadSafetyWriteAssembly
Ancestors
  lowerDloadSafetyAssemblyPremises lowerDloadSafetyTaintWidth
  lowerDloadSafetyMemoryWriteEffects lowerDloadSafetyMemoryCopyEffects
  lowerDloadSafetyEmptyCopy lowerDloadSafetyValues lowerDloadSafetyRelation
  codegenRel contextCodegenRel venomWf ptrDiscipline pointerConfinedDefs memLocDefs venomInst venomExecSemantics venomState finite_map list pred_set

Theorem ld_write_value_nonpointer:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode [MSTORE;MSTORE8;ISTORE] /\
  inst.inst_operands = [a;Var v] ==> v NOTIN fn_pv P fn
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P fn) inst` by fs[fn_ptr_ok_def] >>
  qpat_x_assum `fn_ptr_ok _ _` kall_tac >>
  rpt strip_tac >>
  gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
      mem_write_ops_def, mem_read_ops_def] >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[] >>
  Cases_on `a = Var v` >> simp[]
QED

Theorem ld_copy_length_nonpointer:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [a;b;Var v] ==>
  v NOTIN fn_pv P fn
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P fn) inst` by fs[fn_ptr_ok_def] >>
  qpat_x_assum `fn_ptr_ok _ _` kall_tac >>
  rpt strip_tac >>
  gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
      mem_write_ops_def, mem_read_ops_def] >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[] >>
  Cases_on `a = Var v` >> Cases_on `b = Var v` >> simp[] >>
  rpt strip_tac >> gvs[]
QED

Theorem ld_write_operand_observation:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ MEM inst (fn_insts f.lf_fn) /\
  ~MEM inst.inst_opcode [ASSIGN;PHI;RET;RETFMP;DRET] /\ MEM op inst.inst_operands /\
  tn.t_var = f.lf_tv /\
  eval_operand op f.lf_src = SOME x /\ eval_operand op f.lf_tgt = SOME y ==>
  (op_prov f.lf_H op = NONE ==> word_agree_except (op_taint tn op) x y) /\
  (!a. op_prov f.lf_H op = SOME a ==> ld_wordrel A (SOME a) x y)
Proof
  strip_tac >>
  `!v. op = Var v ==> ~retpc_var f.lf_fn v` by
    (gen_tac >> disch_tac >> irule ld_numeric_operand_nonopaque >>
     simp[] >> qexists_tac `inst` >> gvs[]) >>
  Cases_on `op` >>
  gvs[eval_operand_def, lookup_var_def, op_prov_def, op_taint_def,
      ld_word_agree_empty] >>
  drule_all ld_vars_value >> Cases_on `FLOOKUP f.lf_H s` >> simp[]
QED

Theorem ld_write_operand_defined:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  MEM inst (fn_insts f.lf_fn) /\ MEM op inst.inst_operands /\
  eval_operand op f.lf_tgt = SOME y ==>
  ?x. eval_operand op f.lf_src = SOME x
Proof
  strip_tac >>
  `IS_SOME (eval_operand op f.lf_src)` by
    (drule ld_vars_operand_defined >> disch_then (qspec_then `op` mp_tac) >> simp[] >>
     impl_tac >- (rpt strip_tac >> irule ld_inst_input_ir >> metis_tac[]) >>
     simp[]) >>
  Cases_on `eval_operand op f.lf_src` >> gvs[]
QED

Theorem ld_vars_unselected:
  ld_vars P A f /\ v NOTIN fn_pv P f.lf_fn ==>
  FLOOKUP f.lf_H v = NONE
Proof
  strip_tac >> `v NOTIN FDOM f.lf_H` by
    (fs[ld_vars_def, SUBSET_DEF] >> metis_tac[]) >>
  simp[FLOOKUP_DEF]
QED

Theorem ld_write_scalar_observation:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ MEM inst (fn_insts f.lf_fn) /\
  ~MEM inst.inst_opcode [ASSIGN;PHI;RET;RETFMP;DRET] /\ MEM op inst.inst_operands /\
  tn.t_var = f.lf_tv /\
  eval_operand op f.lf_src = SOME x /\ eval_operand op f.lf_tgt = SOME y /\
  op_prov f.lf_H op = NONE ==>
  word_agree_except (op_taint tn op) x y
Proof
  metis_tac[ld_write_operand_observation]
QED

Theorem ld_write_address_observation:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ MEM inst (fn_insts f.lf_fn) /\
  ~MEM inst.inst_opcode [ASSIGN;PHI;RET;RETFMP;DRET] /\ MEM op inst.inst_operands /\
  tn.t_var = f.lf_tv /\
  eval_operand op f.lf_src = SOME x /\ eval_operand op f.lf_tgt = SOME y /\
  op_taint tn op = {} ==>
  (op_prov f.lf_H op = NONE ==> x=y) /\
  (!a. op_prov f.lf_H op = SOME a ==> ld_wordrel A (SOME a) x y)
Proof
  strip_tac >>
  `((op_prov f.lf_H op = NONE ==> word_agree_except (op_taint tn op) x y) /\
     (!a. op_prov f.lf_H op = SOME a ==> ld_wordrel A (SOME a) x y))` by
    (irule ld_write_operand_observation >> simp[] >> conj_tac
     >- (qexists_tac `inst` >> fs[]) >> metis_tac[]) >>
  gvs[ld_word_agree_empty]
QED

Theorem ld_write_access_classified:
  access_ok lo (ld_erase A o_f H) fn inst s /\
  ~in_revert_forward fn s /\ mem_write_ops inst = SOME ops /\
  MEM (w2n x,n) (source_memory_write_ranges inst s) /\ 0 < n /\
  (op_prov H ops.iao_ofst = NONE ==> x = y) /\
  (!a. op_prov H ops.iao_ofst = SOME a ==> ld_wordrel A (SOME a) x y) /\
  (!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)) ==>
  (w2n x+n <= lo /\ y=x) \/
  (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
    w2n x=b+delta /\ w2n y=c+delta /\ delta+n <= sz)
Proof
  strip_tac >> drule_all ld_write_access_cases >> metis_tac[]
QED

Theorem ld_read_access_classified:
  access_ok lo (ld_erase A o_f H) fn inst s /\
  ~in_revert_forward fn s /\ mem_read_ops inst = SOME ops /\
  MEM (w2n x,n) (source_memory_read_ranges inst s) /\ 0 < n /\
  (op_prov H ops.iao_ofst = NONE ==> x = y) /\
  (!a. op_prov H ops.iao_ofst = SOME a ==> ld_wordrel A (SOME a) x y) /\
  (!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)) ==>
  (w2n x+n <= lo /\ y=x) \/
  (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
    w2n x=b+delta /\ w2n y=c+delta /\ delta+n <= sz)
Proof
  strip_tac >> drule_all ld_read_access_cases >> metis_tac[]
QED

Theorem ld_write2_operands:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  MEM inst (fn_insts f.lf_fn) /\ inst_wf inst /\
  MEM inst.inst_opcode [MSTORE;MSTORE8;ISTORE] /\
  step_inst_base inst f.lf_tgt = OK ts ==>
  ?a v dst dst' x y. inst.inst_operands = [a;v] /\
    inst.inst_outputs = [] /\
    eval_operand a f.lf_src = SOME dst /\
    eval_operand a f.lf_tgt = SOME dst' /\
    eval_operand v f.lf_src = SOME x /\
    eval_operand v f.lf_tgt = SOME y
Proof
  strip_tac >>
  `LENGTH inst.inst_operands = 2 /\ inst.inst_outputs = []` by
    (fs[inst_wf_def] >> rpt strip_tac >> gvs[] >>
     Cases_on `inst.inst_outputs` >> gvs[]) >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >> rename1 `inst.inst_operands = [a;v]` >>
  `?dst' y. eval_operand a f.lf_tgt = SOME dst' /\
            eval_operand v f.lf_tgt = SOME y` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     pure_once_rewrite_tac[step_inst_base_def] >>
     asm_rewrite_tac[opcode_case_def] >>
     simp[exec_write2_def, eval_operands_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[]) >>
  `?dst. eval_operand a f.lf_src = SOME dst` by
    (irule ld_write_operand_defined >> simp[] >> conj_tac
     >- (qexists_tac `inst` >> simp[]) >> metis_tac[]) >>
  `?x. eval_operand v f.lf_src = SOME x` by
    (irule ld_write_operand_defined >> simp[] >> conj_tac
     >- (qexists_tac `inst` >> simp[]) >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ld_write2_taint:
  taint_ok fn tn inst s /\ MEM inst.inst_opcode [MSTORE;MSTORE8;ISTORE] /\
  inst.inst_operands = [a;v] ==>
  op_taint tn a = {} /\ (inst.inst_opcode = MSTORE8 ==> op_taint tn v = {})
Proof
  strip_tac >> qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
  simp[taint_ok_def] >> strip_tac >>
  conj_tac
  >- (first_x_assum (qspec_then `a` mp_tac) >> simp[] >>
      fs[MEM] >> metis_tac[]) >>
  strip_tac >> first_x_assum (qspec_then `v` mp_tac) >> simp[]
QED

Theorem ld_sync_memory_write_effect:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ f.lf_src = s /\ f.lf_tgt = t /\ f.lf_fn = fn /\
  ptr_discipline lo C vs0 /\ fn_shape_ok fn /\ fn_inst_wf fn /\
  s.vs_labels = t.vs_labels /\ ~in_revert_forward fn s /\
  t.vs_alloca_next < dimword(:256) /\
  MEM inst.inst_opcode [MSTORE;MSTORE8;MCOPY] /\
  step_inst fuel C' inst t = OK ts ==>
  ?ss. step_inst fuel C inst s = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := ts;
      lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst s ss tn) ss ts /\
    ld_nonghost (step_taint inst s ss tn) ss ts /\
    step_prov PG G inst ss = G /\
    ss.vs_allocas = s.vs_allocas /\ ss.vs_alloca_next = s.vs_alloca_next /\
    ss.vs_current_bb = s.vs_current_bb /\ ss.vs_prev_bb = s.vs_prev_bb /\
    ss.vs_inst_idx = s.vs_inst_idx /\
    ts.vs_allocas = t.vs_allocas /\ ts.vs_alloca_next = t.vs_alloca_next /\
    ts.vs_current_bb = t.vs_current_bb /\ ts.vs_prev_bb = t.vs_prev_bb /\
    ts.vs_inst_idx = t.vs_inst_idx /\
    (!a. a IN FRANGE f.lf_H ==> a IN FDOM A)
Proof
  strip_tac >>
  `MEM inst (fn_insts fn)` by
    (drule ld_sync_source >> simp[active_inst_def] >> strip_tac >>
     `MEM inst bb.bb_instructions` by metis_tac[MEM_EL] >>
     qpat_x_assum `MEM bb fn.fn_blocks` mp_tac >>
     simp[fn_insts_def] >>
     qspec_tac (`fn.fn_blocks`, `bbs`) >> Induct >>
     simp[fn_insts_blocks_def] >> metis_tac[]) >>
  `fn_ptr_ok P fn` by
    (qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ld_sync_def] >> simp[EVERY_MEM] >>
     strip_tac >> metis_tac[]) >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule ld_sync_ghosts >> simp[] >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  `access_ok lo G fn inst s` by metis_tac[ld_sync_access_ok] >>
  `taint_ok fn tn inst s` by metis_tac[ld_sync_taint_ok] >>
  `inst_wf inst` by
    (drule ld_sync_source >> simp[active_inst_def] >> strip_tac >>
     fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[MEM_EL]) >>
  `FDOM A = ld_slots A (f::fs) /\ EVERY (ld_maps A) (f::fs)` by
    (qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ld_sync_def] >> simp[EVERY_MEM] >>
     strip_tac >> metis_tac[]) >>
  `!a. a IN FRANGE f.lf_H ==> a IN FDOM A` by
    (fs[ld_global_def] >> metis_tac[]) >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)` by
    (drule ld_alloc_target_no_wrap >> simp[] >> metis_tac[]) >>
  `inst.inst_opcode <> INVOKE` by
    (qpat_x_assum `MEM inst.inst_opcode _` mp_tac >> simp[] >> strip_tac >> gvs[]) >>
  gvs[step_inst_non_invoke]
  >- suspend "mstore"
  >- suspend "mstore8"
  >> suspend "mcopy"
QED

Resume ld_sync_memory_write_effect[mstore]:
  `MEM inst.inst_opcode [MSTORE;MSTORE8;ISTORE]` by simp[] >>
  drule_all ld_write2_operands >> strip_tac >>
  `op_prov f.lf_H v = NONE` by
    (Cases_on `v` >> simp[op_prov_def] >>
     `s NOTIN fn_pv P f.lf_fn` by
       (irule ld_write_value_nonpointer >> simp[] >> qexistsl_tac [`a`,`inst`] >> simp[]) >>
     irule ld_vars_unselected >> metis_tac[]) >>
  `word_agree_except (op_taint tn v) x y` by
    (irule ld_write_scalar_observation >> simp[] >>
     qexistsl_tac [`A`,`P`,`f`,`inst`] >> simp[]) >>
  `op_taint tn a = {}` by metis_tac[ld_write2_taint] >>
  `(op_prov f.lf_H a = NONE ==> dst = dst') /\
    (!k. op_prov f.lf_H a = SOME k ==> ld_wordrel A (SOME k) dst dst')` by
    (irule ld_write_address_observation >> simp[] >> conj_tac
     >- (qexists_tac `tn` >> simp[]) >> conj_tac
     >- (qexists_tac `inst` >> simp[]) >> metis_tac[]) >>
  Q.SUBGOAL_THEN `((w2n dst+32 <= lo /\ dst'=dst) \/
    (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
      w2n dst=b+delta /\ w2n dst'=c+delta /\ delta+32 <= sz))` ASSUME_TAC >-
    (irule ld_write_access_classified >> simp[] >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`f.lf_H`,`f.lf_fn`,`inst`] >>
     simp[mem_write_ops_def] >> qexists_tac `f.lf_src` >>
     simp[mem_write_ops_def, source_memory_write_ranges_def,
          fixed_source_write_range_def, eval_operands_def]) >>
  `op_taint tn v SUBSET {j | j < 32}` by
    (drule ld_sync_source >> strip_tac >> irule ld_reachable_op_taint_width >> metis_tac[]) >>
  `tn.t_var = f.lf_tv /\ EVERY (ld_maps A) (f::fs)` by simp[] >>
  drule_all ld_mstore_effect >> strip_tac >>
  qexists_tac `ss` >> simp[]
QED
Resume ld_sync_memory_write_effect[mstore8]:
  `MEM inst.inst_opcode [MSTORE;MSTORE8;ISTORE]` by simp[] >>
  drule_all ld_write2_operands >> strip_tac >>
  `op_taint tn a = {} /\ op_taint tn v = {}` by metis_tac[ld_write2_taint] >>
  `op_prov f.lf_H v = NONE` by
    (Cases_on `v` >> simp[op_prov_def] >>
     `s NOTIN fn_pv P f.lf_fn` by
       (irule ld_write_value_nonpointer >> simp[] >> qexistsl_tac [`a`,`inst`] >> simp[]) >>
     irule ld_vars_unselected >> metis_tac[]) >>
  `word_agree_except (op_taint tn v) x y` by
    (irule ld_write_scalar_observation >> simp[] >>
     qexistsl_tac [`A`,`P`,`f`,`inst`] >> simp[]) >>
  `x = y` by metis_tac[ld_word_agree_empty] >>
  `(op_prov f.lf_H a = NONE ==> dst = dst') /\
    (!k. op_prov f.lf_H a = SOME k ==> ld_wordrel A (SOME k) dst dst')` by
    (irule ld_write_address_observation >> simp[] >> conj_tac
     >- (qexists_tac `tn` >> simp[]) >> conj_tac
     >- (qexists_tac `inst` >> simp[]) >> metis_tac[]) >>
  Q.SUBGOAL_THEN `((w2n dst+1 <= lo /\ dst'=dst) \/
    (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
      w2n dst=b+delta /\ w2n dst'=c+delta /\ delta+1 <= sz))` ASSUME_TAC >-
    (irule ld_write_access_classified >> simp[] >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`f.lf_H`,`f.lf_fn`,`inst`] >>
     simp[mem_write_ops_def] >> qexists_tac `f.lf_src` >>
     simp[mem_write_ops_def, source_memory_write_ranges_def,
          fixed_source_write_range_def, eval_operands_def]) >>
  `tn.t_var = f.lf_tv /\ EVERY (ld_maps A) (f::fs) /\
    (w2w x : word8) = w2w y` by simp[] >>
  drule_all ld_mstore8_effect >> strip_tac >>
  qexists_tac `ss` >> simp[]
QED
Resume ld_sync_memory_write_effect[mcopy]:
  `LENGTH inst.inst_operands = 3 /\ inst.inst_outputs = []` by
    (fs[inst_wf_def] >> Cases_on `inst.inst_outputs` >> gvs[]) >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  `t = []` by (fs[] >> Cases_on `t` >> gvs[]) >> gvs[] >>
  rename1 `inst.inst_operands = [d;r;n]` >>
  `?dst' src' len'. eval_operand d f.lf_tgt = SOME dst' /\
    eval_operand r f.lf_tgt = SOME src' /\ eval_operand n f.lf_tgt = SOME len'` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     pure_once_rewrite_tac[step_inst_base_def] >>
     asm_rewrite_tac[opcode_case_def] >>
     simp[AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
  `?dst. eval_operand d f.lf_src = SOME dst` by
    (irule ld_write_operand_defined >> simp[] >> conj_tac
     >- (qexists_tac `inst` >> simp[]) >> metis_tac[]) >>
  `?src. eval_operand r f.lf_src = SOME src` by
    (irule ld_write_operand_defined >> simp[] >> conj_tac
     >- (qexists_tac `inst` >> simp[]) >> metis_tac[]) >>
  `?len. eval_operand n f.lf_src = SOME len` by
    (irule ld_write_operand_defined >> simp[] >> conj_tac
     >- (qexists_tac `inst` >> simp[]) >> metis_tac[]) >>
  `!op. MEM op inst.inst_operands ==> op_taint tn op = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     simp[taint_ok_def] >> metis_tac[]) >>
  `op_prov f.lf_H n = NONE` by
    (Cases_on `n` >> simp[op_prov_def] >>
     `s NOTIN fn_pv P f.lf_fn` by
       (irule ld_copy_length_nonpointer >> simp[] >> qexistsl_tac [`d`,`r`,`inst`] >> simp[]) >>
     irule ld_vars_unselected >> metis_tac[]) >>
  `word_agree_except (op_taint tn n) len len'` by
    (irule ld_write_scalar_observation >> simp[] >>
     qexistsl_tac [`A`,`P`,`f`,`inst`] >> simp[]) >>
  `len = len'` by metis_tac[ld_word_agree_empty, MEM] >>
  gvs[] >>
  `tn.t_var = f.lf_tv /\ EVERY (ld_maps A) (f::fs)` by simp[] >>
  Cases_on `w2n len = 0`
  >- (drule_all ld_mcopy_zero_effect >> strip_tac >> qexists_tac `ss` >> simp[]) >>
  `!op x y. MEM op inst.inst_operands /\
      eval_operand op f.lf_src = SOME x /\ eval_operand op f.lf_tgt = SOME y ==>
      (op_prov f.lf_H op = NONE ==> x=y) /\
      (!k. op_prov f.lf_H op = SOME k ==> ld_wordrel A (SOME k) x y)` by
    (rpt gen_tac >> strip_tac >> irule ld_write_address_observation >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexists_tac `tn` >> conj_tac >- first_assum ACCEPT_TAC >>
                 metis_tac[MEM]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexists_tac `inst` >> asm_rewrite_tac[] >> simp[]) >>
     qexists_tac `P` >> first_assum ACCEPT_TAC) >>
  Q.SUBGOAL_THEN `((w2n dst+w2n len <= lo /\ dst'=dst) \/
    (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
      w2n dst=b+delta /\ w2n dst'=c+delta /\ delta+w2n len <= sz))` ASSUME_TAC >-
    (irule ld_write_access_classified >> simp[] >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`f.lf_H`,`f.lf_fn`,`inst`] >>
     simp[mem_write_ops_def] >> qexists_tac `f.lf_src` >>
     simp[source_memory_write_ranges_def, sized_source_write_range_def,
          eval_operands_def] >> metis_tac[MEM]) >>
  Q.SUBGOAL_THEN `((w2n src+w2n len <= lo /\ src'=src) \/
    (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
      w2n src=b+delta /\ w2n src'=c+delta /\ delta+w2n len <= sz))` ASSUME_TAC >-
    (irule ld_read_access_classified >> simp[] >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`f.lf_H`,`f.lf_fn`,`inst`] >>
     simp[mem_read_ops_def] >> qexists_tac `f.lf_src` >>
     simp[source_memory_read_ranges_def, eval_operands_def] >> metis_tac[MEM]) >>
  drule_all ld_mcopy_effect >> strip_tac >> qexists_tac `ss` >> simp[]
QED
Finalise ld_sync_memory_write_effect
