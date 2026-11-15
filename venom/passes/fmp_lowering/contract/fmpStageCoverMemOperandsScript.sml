(* Operand availability boundary for memory coverage. *)
Theory fmpStageCoverMemOperands
Ancestors
  fmpStageOpBase fmpStageRel o1PassContract ptrDiscipline
  o1ContractSimplifyCfgSrcFrame simplifyCfgAvailability
  unitTransformDefs unitShapeDefs venomWf venomState list
  ptrStaticDiscipline memLocDefs pointerConfinedDefs pred_set finite_map
  frameViewFacts o1LowerDloadAddressArithmetic words arithmetic

Theorem fmp_stage_var_defined:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode <> PHI /\ MEM (Var v) inst.inst_operands ==>
  IS_SOME (lookup_var v s)
Proof
  strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  `?r. fn_entry_state fn r /\ frame_reach C fn r inst s` by
    (irule scfg_frame_reachable_entry_root >>
     conj_tac
     >- (gvs[fmp_stage_ctx_def, o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >>
         metis_tac[venomInstTheory.lookup_function_MEM]) >>
     qexistsl_tac [`G`, `PG`, `stk`, `tn`, `vs`] >>
     gvs[fmp_stage_ctx_def, o1_run_state_ok_def, o1_initial_state_ok_def]) >>
  irule scfg_frame_operand_defined >>
  gvs[o1_fn_shape_def, make_ssa_input_ok_def] >> metis_tac[]
QED

Theorem fmp_static_descriptor_size_nonpointer[local]:
  ptr_use_static_ok P pv inst /\
  (mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops) /\
  ops.iao_max_size = SOME (Var v) ==> v NOTIN pv
Proof
  strip_tac >> disch_tac >>
  Cases_on `inst.inst_opcode` >>
  FIRST [gvs[mem_read_ops_def, mem_write_ops_def, AllCaseEqs()]] >>
  qpat_x_assum `ptr_use_static_ok _ _ _`
    (mp_tac o REWRITE_RULE [ptr_use_static_ok_def]) >>
  disch_then (CONJUNCTS_THEN2 kall_tac (qspec_then `v` mp_tac)) >>
  (impl_tac >- (simp[is_pointer_preserving_op_def] >>
                 metis_tac[MEM_REVERSE, MEM])) >>
  strip_tac >>
  gvs[mem_read_ops_def, mem_write_ops_def, AllCaseEqs()] >>
  gvs[AllCaseEqs()] >>
  qpat_x_assum `FILTER _ _ = _`
    (mp_tac o AP_TERM ``REVERSE : operand list -> operand list``) >>
  pure_rewrite_tac[GSYM FILTER_REVERSE] >>
  asm_rewrite_tac[FILTER, REVERSE_DEF, CONS_11] >> simp[]
QED

Theorem fmp_stage_operand_back[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  inst.inst_opcode <> PHI /\ MEM op inst.inst_operands /\
  (!v. op = Var v ==> ~retpc_var fn v) /\
  eval_operand op t = SOME y ==>
  ?x. eval_operand op s = SOME x /\
      fmp_value_rel sm (op_prov G op) (op_taint tn op) x y
Proof
  strip_tac >>
  `?x. eval_operand op s = SOME x` by
    (Cases_on `op`
     >- simp[eval_operand_def]
     >- (rename1 `MEM (Var v) inst.inst_operands` >>
         drule_all fmp_stage_var_defined >>
         Cases_on `lookup_var v s` >> simp[eval_operand_def]) >>
     `s.vs_labels = t.vs_labels` by
       gvs[fmp_stage_rel_def, fmp_frame_rel_def] >>
     gvs[eval_operand_def]) >>
  drule_all fmp_stage_operand >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem fmp_stage_clean_operand_equal[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  inst.inst_opcode <> PHI /\ MEM op inst.inst_operands /\
  (!v. op = Var v ==> ~retpc_var fn v) /\
  op_prov G op = NONE /\ op_taint tn op = {} ==>
  eval_operand op s = eval_operand op t
Proof
  strip_tac >>
  Cases_on `eval_operand op s` >> Cases_on `eval_operand op t` >> simp[]
  >- (drule_all fmp_stage_operand_back >> simp[])
  >- (drule_all fmp_stage_operand >> simp[]) >>
  drule_all fmp_stage_operand >>
  simp[fmp_value_rel_def] >> strip_tac >>
  metis_tac[o1LowerDloadRelocationKernelTheory.ld_value_agree_clean]
QED

Theorem fmp_stage_size_equal:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  (mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops) /\
  ops.iao_max_size = SOME szop ==>
  eval_operand szop s = eval_operand szop t
Proof
  strip_tac >> (
  drule_all fmp_stage_frame_facts >> strip_tac >>
  `FDOM G SUBSET fn_pv P fn` by metis_tac[fmp_stage_prov_support] >>
  `ptr_use_static_ok P (fn_pv P fn) inst` by
    (gvs[EVERY_MEM, fn_static_ptr_ok_def] >> metis_tac[]) >>
  `!v. szop = Var v ==> MEM (Var v) inst.inst_operands` by
    (rpt strip_tac >> Cases_on `inst.inst_opcode` >>
     FIRST [gvs[mem_read_ops_def, mem_write_ops_def, AllCaseEqs()]] >>
     metis_tac[MEM_REVERSE, MEM]) >>
  Cases_on `szop` >- simp[eval_operand_def]
  >- (gvs[] >> rename1 `MEM (Var v) inst.inst_operands` >>
  `v NOTIN fn_pv P fn` by metis_tac[fmp_static_descriptor_size_nonpointer] >>
  `op_prov G (Var v) = NONE` by
    (gvs[op_prov_def, SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  `~MEM inst.inst_opcode [ASSIGN;PHI;RET;RETFMP;DRET]` by
    (Cases_on `inst.inst_opcode` >>
     FIRST [gvs[mem_read_ops_def, mem_write_ops_def, AllCaseEqs()]]) >>
  `~retpc_var fn v` by
    metis_tac[ordinary_operand_not_retpc, o1_fn_shape_def, fn_shape_ok_def, MEM] >>
  `op_taint tn (Var v) = {}` by
    (Cases_on `inst.inst_opcode` >>
     FIRST [gvs[mem_read_ops_def, mem_write_ops_def, AllCaseEqs()]] >>
     fs[taint_ok_def] >> metis_tac[MEM, MEM_REVERSE]) >>
  fs[] >>
  `!w. Var v = Var w ==> ~retpc_var fn w` by simp[] >>
  drule_all fmp_stage_clean_operand_equal >> simp[]) >>
  gvs[fmp_stage_rel_def, fmp_frame_rel_def, eval_operand_def])
QED

Theorem fmp_stage_offset_observation:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  (mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops) /\
  eval_operand ops.iao_ofst t = SOME y ==>
  ?x. eval_operand ops.iao_ofst s = SOME x /\
      fmp_value_rel sm (op_prov G ops.iao_ofst) {} x y
Proof
  strip_tac >> (
  drule_all fmp_stage_frame_facts >> strip_tac >>
  `~MEM inst.inst_opcode [ASSIGN;PHI;RET;RETFMP;DRET]` by
    (Cases_on `inst.inst_opcode` >>
     gvs[mem_read_ops_def, mem_write_ops_def, AllCaseEqs()]) >>
  `MEM ops.iao_ofst inst.inst_operands` by
    (Cases_on `inst.inst_opcode` >>
     gvs[mem_read_ops_def, mem_write_ops_def, AllCaseEqs()] >>
     metis_tac[MEM, MEM_REVERSE]) >>
  `!v. ops.iao_ofst = Var v ==> ~retpc_var fn v` by
    (rpt strip_tac >> fs[] >>
     metis_tac[ordinary_operand_not_retpc, o1_fn_shape_def, fn_shape_ok_def]) >>
  `op_taint tn ops.iao_ofst = {}` by
    (Cases_on `inst.inst_opcode` >>
     gvs[mem_read_ops_def, mem_write_ops_def, AllCaseEqs()] >>
     fs[taint_ok_def] >> metis_tac[MEM, MEM_REVERSE, CONS_11]) >>
  fs[] >> drule_all fmp_stage_operand_back >> simp[])
QED

(* Safety consequence of relocating a range; unlike slice transport this
   needs no memory agreement and returns only the target coverage bound. *)
Theorem fmp_value_range_covered:
  fmp_sites_ok sm fmp0 raw0 lo raw /\ lo <= w2n raw /\
  fmp_value_rel sm h {} x y /\
  (len <> 0 /\ (eom < w2n x + len \/ h <> NONE) ==>
    ?b z. h = SOME (b,z) /\ b <= w2n x /\ w2n x + len <= b+z) ==>
  len = 0 \/ w2n y + len <= eom \/ fmp0 <= w2n y
Proof
  strip_tac >> Cases_on `len = 0` >> simp[] >>
  Cases_on `h = NONE`
  >- (gvs[fmp_value_rel_def] >>
      `x = y` by metis_tac[o1LowerDloadRelocationKernelTheory.ld_value_agree_clean] >>
      gvs[] >> Cases_on `eom < w2n y + len` >> gvs[]) >>
  `?b z. h = SOME (b,z) /\ b <= w2n x /\ w2n x + len <= b+z` by metis_tac[] >>
  gvs[fmp_value_rel_def,
      o1LowerDloadRelocationKernelTheory.ld_value_agree_pointer,
      FLOOKUP_fmp_ld_sites, AllCaseEqs()] >>
  rename1 `FLOOKUP sm (b,z) = SOME (c,id)` >>
  `fmp0 <= c /\ b+z < dimword (:256) /\ c+z < dimword (:256)` by
    (fs[fmp_sites_ok_def] >> metis_tac[w2n_lt, LESS_EQ_LESS_TRANS]) >>
  `w2n (x+n2w c-n2w b) = c+(w2n x-b)` by
    (irule lower_dload_translate_endpoint >> simp[] >>
     qexists_tac `z` >> simp[]) >>
  simp[]
QED
