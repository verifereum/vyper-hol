(*
 * Paired-prefix extension for the N11 opcode family (EXTCODECOPY).
 *)
Theory concretizePtrExtcodecopyFamily
Ancestors
  concretizePtrStorageReadProducer concretizePtrBufferCopyContent
  concretizePtrWriteClassification concretizePtrRequestHistory concretizePtrTaintContent
  concretizePtrPrefixLedger ptrDiscipline codegenRel memLocDefs
  concretizePtrOpaqueRetpc concretizePtrReturnTransport
  concretizePtrValueTransport pointerConfinedDefs
  venomExecSemantics venomState venomInst list words

Theorem ptr_extcodecopy_account_code[local]:
  ptr_history_content tn s t ==>
  (lookup_account addr s.vs_accounts).code =
  (lookup_account addr t.vs_accounts).code
Proof
  strip_tac >> drule ptr_history_content_current >> strip_tac >>
  drule ptr_taint_content_account >>
  simp[vfmStateTheory.lookup_account_def] >>
  disch_then (qspec_then `addr` mp_tac) >>
  disch_then (mp_tac o AP_TERM ``\a:account_state. a.code``) >> simp[]
QED

Theorem ptr_extcodecopy_success[local]:
  inst.inst_opcode = EXTCODECOPY /\
  inst.inst_operands = [a;d;r;n] ==>
  (step_inst fuel C inst s = OK post <=>
   ?addr dst src sz.
     eval_operand a s = SOME addr /\ eval_operand d s = SOME dst /\
     eval_operand r s = SOME src /\ eval_operand n s = SOME sz /\
     post = write_memory_with_expansion (w2n dst)
       (TAKE (w2n sz) (DROP (w2n src)
         (lookup_account (w2w addr) s.vs_accounts).code ++
         REPLICATE (w2n sz) 0w)) s)
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem ptr_extcodecopy_footprint[local]:
  inst.inst_opcode = EXTCODECOPY /\ inst.inst_operands = [a;d;r;n] /\
  eval_operand a s = SOME addr /\ eval_operand d s = SOME dst /\
  eval_operand r s = SOME src /\ eval_operand n s = SOME sz ==>
  (i IN range_bytes (step_writes inst s post) <=>
   w2n dst <= i /\ i < w2n dst + w2n sz)
Proof
  simp[step_writes_def, source_memory_write_ranges_def,
       sized_source_write_range_def, range_bytes_def,
       arithmeticTheory.ADD_COMM]
QED

Theorem ptr_extcodecopy_scalar_discipline[local]:
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\
  (!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P fn) /\
  inst.inst_opcode = EXTCODECOPY /\ inst.inst_operands = [a;d;r;n] ==>
  EVERY (ptr_nonopaque_operand fn) [a;d;r;n] /\
  EVERY (\op. op_taint tn op = {}) [a;d;r;n] /\
  EVERY (\op. op_prov TG op = NONE) [a;r;n]
Proof
  strip_tac >>
  `EVERY (ptr_nonopaque_operand fn) inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[]) >>
  `EVERY (\op. op_taint tn op = {}) inst.inst_operands` by
    (fs[taint_ok_def, EVERY_MEM] >> metis_tac[]) >>
  simp[] >>
  `!v. MEM (Var v) [a;r;n] ==> v NOTIN fn_pv P fn` by
    (`ptr_use_ok P (fn_pv P fn) inst` by
       (fs[fn_ptr_ok_def] >> metis_tac[]) >>
     qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def,
          mem_write_ops_def, mem_read_ops_def] >> strip_tac >>
     gen_tac >> disch_tac >> disch_tac >>
     first_x_assum (qspec_then `v` mp_tac) >>
     Cases_on `a = Var v` >> Cases_on `d = Var v` >>
     Cases_on `r = Var v` >> Cases_on `n = Var v` >>
     fs[]) >>
  `EVERY (\op. op_prov TG op = NONE) [a;r;n]` by
    (pure_rewrite_tac[EVERY_MEM] >> qx_gen_tac `op` >> strip_tac >>
     Cases_on `op` >> simp[op_prov_def] >>
     Cases_on `FLOOKUP TG s'` >> simp[] >> metis_tac[]) >>
  gvs[]
QED

Theorem ptr_extcodecopy_mixed_execution[local]:
  inst.inst_opcode = EXTCODECOPY /\ inst.inst_operands = [a;d;r;n] /\
  ptr_mixed_vars births positions TG tn f g s t /\ ptr_history_content tn s t /\
  EVERY (ptr_nonopaque_operand f) [a;d;r;n] /\
  EVERY (\op. op_prov TG op = NONE /\ op_taint tn op = {}) [a;r;n] /\
  step_inst fuel Ct inst t = OK postt ==>
  ?addr dst dt src sz bytes post.
    eval_operand a s = SOME addr /\ eval_operand a t = SOME addr /\
    eval_operand d s = SOME dst /\ eval_operand d t = SOME dt /\
    eval_operand r s = SOME src /\ eval_operand r t = SOME src /\
    eval_operand n s = SOME sz /\ eval_operand n t = SOME sz /\
    LENGTH bytes = w2n sz /\
    step_inst 0 C inst s = OK post /\
    post = write_memory_with_expansion (w2n dst) bytes s /\
    postt = write_memory_with_expansion (w2n dt) bytes t /\
    (!i. i < w2n sz ==>
      read_byte (w2n dst + i) post.vs_memory =
      read_byte (w2n dt + i) postt.vs_memory)
Proof
  strip_tac >>
  `s.vs_labels = t.vs_labels` by metis_tac[ptr_history_content_labels] >>
  `eval_operands [a;r;n] s = eval_operands [a;r;n] t` by
    (irule ptr_mixed_scalar_operands_equal >> simp[] >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all ptr_extcodecopy_success >> strip_tac >>
  qpat_x_assum `step_inst fuel Ct inst t = OK postt` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  `ptr_lookup_transport births positions (op_prov TG d) (op_taint tn d)
    (eval_operand d s) (eval_operand d t)` by
    (irule ptr_mixed_vars_eval >>
     rpt (goal_assum (drule_at Any)) >> fs[]) >>
  gvs[ptr_lookup_transport_some_right, eval_operands_def, AllCaseEqs()] >>
  qexists_tac `TAKE (w2n sz) (DROP (w2n src)
      (lookup_account (w2w addr) t.vs_accounts).code ++ REPLICATE (w2n sz) 0w)` >>
  simp[LENGTH_TAKE] >>
  `!addr. (lookup_account addr s.vs_accounts).code =
          (lookup_account addr t.vs_accounts).code` by
    metis_tac[ptr_extcodecopy_account_code] >>
  simp[] >> rpt strip_tac >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule ptr_payload_write_content >> simp[LENGTH_TAKE]
QED

Theorem ptr_extcodecopy_post_content[local]:
  inst.inst_opcode = EXTCODECOPY /\ inst.inst_outputs = [] /\
  ptr_mixed_vars births positions TG tn f g s t /\
  ptr_history_content tn s t ==>
  step_prov PT TG inst (write_memory_with_expansion dst bytes s) = TG /\
  ptr_mixed_vars births positions TG
    (step_taint inst s (write_memory_with_expansion dst bytes s) tn) f g
    (write_memory_with_expansion dst bytes s with vs_inst_idx := k)
    (write_memory_with_expansion dt bytes t with vs_inst_idx := kt) /\
  ptr_history_content
    (step_taint inst s (write_memory_with_expansion dst bytes s) tn)
    (write_memory_with_expansion dst bytes s with vs_inst_idx := k)
    (write_memory_with_expansion dt bytes t with vs_inst_idx := kt)
Proof
  strip_tac >>
  conj_tac >- simp[step_prov_def, set_prov_def, finite_mapTheory.DRESTRICT_UNIV] >>
  reverse conj_tac
  >- (simp[write_memory_with_expansion_def] >>
      irule ptr_history_content_masks >> qexists_tac `tn` >>
      simp[step_taint_def, set_var_taint_def, adopt_reset_def,
           store_taint_def, imm_taint_def]) >>
  irule ptr_mixed_vars_fields >>
  rpt (goal_assum (drule_at Any)) >>
  simp[write_memory_with_expansion_def, step_taint_def, set_var_taint_def,
       finite_mapTheory.DRESTRICT_UNIV]
QED

Theorem ptr_paired_extcodecopy_prefix_normalize:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  LIST_REL (ptr_paired_code R lp positions) C.ctx_functions C'.ctx_functions /\
  EVERY (\f. fn_inst_wf f /\ retpc_shape_ok f /\ opaque_use_ok f /\
    first_block_no_phi f /\ EVERY bb_well_formed f.fn_blocks /\
    ALL_DISTINCT (fn_labels f) /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions /\
  (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name) /\
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode <> NOP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt /\ MEM a.po_inst.inst_opcode [EXTCODECOPY] ==>
  ?delta z tokens' registry' births' PT' TG' saved' entries' snapshots calls' ws'.
    delta <> [] /\ LENGTH snapshots = LENGTH delta /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ delta) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens' registry' births' PT' TG' saved' entries'
      (H ++ snapshots) calls' ws' /\
    z.po_inst.inst_opcode <> NOP /\
    zt.po_inst = concretize_inst_with_positions (lp z.po_fn) z.po_inst
Proof
  cheat
QED

