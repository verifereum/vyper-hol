(*
 * Paired-prefix extension for the N1 opcode family (ADD; SUB).
 *)
Theory concretizePtrAffineFamily
Ancestors
  concretizePtrStorageReadProducer concretizePtrAffineTransport
  concretizePtrOpaqueRetpc concretizePtrValueTransport ptrDiscipline
  venomExecSemantics finite_map list words

Theorem ptr_mixed_affine_execution_back[local]:
  ptr_mixed_vars births positions TG tn f g s t /\
  s.vs_labels = t.vs_labels /\
  ptr_nonopaque_operand f x /\ ptr_nonopaque_operand f y /\
  inst.inst_operands = [x;y] /\ inst.inst_outputs = [out] /\
  MEM inst.inst_opcode [ADD;SUB] /\
  (inst.inst_opcode = ADD ==> op_prov TG x = NONE \/ op_prov TG y = NONE) /\
  (inst.inst_opcode = SUB ==> op_prov TG y = NONE) /\
  op_taint tn x = {} /\ op_taint tn y = {} /\ ~retpc_var f out /\
  step_inst fuel Ct inst t = OK t' ==>
  ?sv tv. step_inst 0 C inst s = OK (update_var out sv s) /\
    t' = update_var out tv t /\
    ptr_mixed_vars births positions
      (step_prov PT TG inst (update_var out sv s))
      (step_taint inst s (update_var out sv s) tn)
      f g (update_var out sv s) t'
Proof
  strip_tac >>
  `ptr_lookup_transport births positions (op_prov TG x) {}
     (eval_operand x s) (eval_operand x t)` by
    (metis_tac[ptr_mixed_vars_eval]) >>
  `ptr_lookup_transport births positions (op_prov TG y) {}
     (eval_operand y s) (eval_operand y t)` by
    (metis_tac[ptr_mixed_vars_eval]) >>
  gvs[MEM] >>
  gvs[ptr_affine_step, exec_pure2_def, AllCaseEqs()] >>
  gvs[ptr_lookup_transport_some_right] >>
  qmatch_goalsub_abbrev_tac `update_var out sv s` >>
  qmatch_goalsub_abbrev_tac `update_var out tv t` >>
  qexistsl_tac [`sv`, `tv`] >> simp[] >>
  drule ptr_mixed_vars_update >> disch_then irule >> simp[] >>
  simp[step_prov_def, out_prov_def, first_prov_def, set_prov_def,
       step_taint_def, out_taint_def, set_var_taint_def, op_taint_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  Cases_on `op_prov TG x` >> Cases_on `op_prov TG y` >>
  gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, ptr_value_transport_scalar_empty,
      Abbr `sv`, Abbr `tv`] >>
  rpt conj_tac >> rpt strip_tac >>
  fs[ptr_mixed_vars_def, op_taint_def] >>
  metis_tac[ptr_value_transport_add_left, ptr_value_transport_add_right,
            ptr_value_transport_sub_right, WORD_ADD_COMM]
QED

Theorem ptr_paired_affine_prefix_normalize:
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
  ptr_chrono_step C' at zt /\ MEM a.po_inst.inst_opcode [ADD; SUB] ==>
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

