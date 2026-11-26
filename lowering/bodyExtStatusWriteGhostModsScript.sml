(* The successful CALL cleans only its actual return-data window. *)
Theory bodyExtStatusWriteGhostMods
Ancestors
  bodyFullExtCallDispatch bodyFullShadowBodyInv bodyFullRawCallCallStorage
  robustCopyTransportPtr appendStorageGhostPtr decoderGhostFramePtr
  exprSimProps[qualified,ignore_grammar] valueEncodingProps abiDecodeStaticProps
  loweringStateRelDefs exprLoweringProps bodyPtrDefs ptrDiscipline codegenRel
  memLocDefs contextCodegenRel
  venomState venomInst venomExecSemantics finite_map pred_set words list arithmetic

Theorem status_write_ghost_jump[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn (jump_to lbl (next_inst u)) <=>
  ghost_inv_at_mods D lo d cenv cx es G tn u
Proof
  Cases_on `d`
  >- simp[ghost_inv_at_mods_def, jump_to_def, next_inst_def, ptr_covers_def,
          lookup_var_def, stor_taint_ok_at_def, allocas_from_def, return_buf_ptr_def] >>
  PairCases_on `x` >>
  simp[ghost_inv_at_mods_def, jump_to_def, next_inst_def, ptr_covers_def,
       lookup_var_def, stor_taint_ok_at_def, allocas_from_def, return_buf_ptr_def]
QED

Theorem status_write_local_value[local]:
  local_ptrs_rel func cenv scopes s /\
  lookup_scopes name scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w /\
  (!m. mem_agree_outside dirty s.vs_memory m ==>
      val_in_memory entry.type entry.value (w2n w) m) /\
  regions_disjoint dst (LENGTH bytes) (w2n w) sz /\
  mem_agree_outside (dirty DIFF {i | dst <= i /\ i < dst + LENGTH bytes})
    (write_memory_with_expansion dst bytes s).vs_memory mem ==>
  val_in_memory entry.type entry.value (w2n w) mem
Proof
  strip_tac >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    (qpat_assum `local_ptrs_rel _ _ _ _` (mp_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     strip_tac >> first_x_assum drule_all >> simp[]) >>
  `val_footprint entry.type entry.value <= sz` by
    (drule exprSimPropsTheory.val_footprint_le >> decide_tac) >>
  irule robust_val_in_memory_exterior_frame >> simp[] >>
  qexistsl [`s.vs_memory`, `(write_memory_with_expansion dst bytes s).vs_memory`,
            `dirty`, `dirty DIFF {i | dst <= i /\ i < dst + LENGTH bytes}`,
            `{i | dst <= i /\ i < dst + LENGTH bytes}`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> irule write_memory_mem_bytes_at_disjoint >> decide_tac) >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem status_write_low_prefix[local]:
  bytes = [] \/ lo <= dst ==>
  mem_bytes_at 0 lo (write_memory_with_expansion dst bytes s).vs_memory =
  mem_bytes_at 0 lo s.vs_memory
Proof
  strip_tac >> irule mem_bytes_at_bytewise >> simp[] >> rpt strip_tac >>
  irule write_memory_mem_bytes_at_disjoint >> simp[] >> decide_tac
QED

Theorem status_clean_write_ghost_mods[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  local_ptrs_rel func cenv es.scopes s /\ local_ptrs_reserved cenv sp /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sp x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sp x) /\
  (!x. not_fresh_at sp x ==>
     FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x) /\
     lookup_var x u = lookup_var x s) /\
  ee.scopes = es.scopes /\
  u.vs_memory = (write_memory_with_expansion dst bytes s).vs_memory /\
  tu.t_mem = tn.t_mem DIFF {i | dst <= i /\ i < dst + LENGTH bytes} /\
  (bytes = [] \/ lo <= dst) /\
  (!name a len. local_region cenv es.scopes s name a len ==>
     regions_disjoint dst (LENGTH bytes) a len) /\
  u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
  stor_taint_ok_at D tu u ==>
  ghost_inv_at_mods D lo d cenv cx ee Gu tu u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `mem_bytes_at 0 lo u.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (simp[] >> irule status_write_low_prefix >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `bytes = [] \/ lo <= dst` kall_tac >>
  `!p sz. not_fresh_at sp p /\ ptr_covers G tn p s sz ==>
          ptr_covers Gu tu p u sz` by
    (rpt strip_tac >> irule ptr_covers_old_transport >>
     goal_assum (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
     qexists `sp` >> simp[]) >>
  fs[ghost_inv_at_mods_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sp p` by metis_tac[local_ptrs_reserved_def] >>
      qpat_assum `!name entry p sz. _` (drule_all_then strip_assume_tac) >>
      conj_tac >- metis_tac[] >>
      rpt gen_tac >> strip_tac >>
      `lookup_var p s = SOME w` by metis_tac[] >>
      `local_region cenv es.scopes s name (w2n w) sz` by
        (simp[local_region_def] >> metis_tac[]) >>
      `regions_disjoint dst (LENGTH bytes) (w2n w) sz` by
        (qpat_assum `!name a len. local_region _ _ _ _ _ _ ==> _` drule >> simp[]) >>
      irule status_write_local_value >>
      goal_assum (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
      goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >>
      simp[] >> qexistsl [`bytes`, `tn.t_mem`, `dst`] >> simp[]) >>
  conj_tac
  >- (Cases_on `d` >> fs[return_buf_ptr_def] >>
      PairCases_on `x` >> gvs[return_buf_ptr_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[local_ptrs_reserved_def] >>
  fs[allocas_from_def] >> first_assum ACCEPT_TAC
QED

Theorem extcall_dispatch_write_ghost_mods:
  inst.inst_opcode = (if stat then STATICCALL else CALL) /\
  inst.inst_operands = (if stat then [g;a;dp;dl;rp;rl] else [g;a;v;dp;dl;rp;rl]) /\
  inst.inst_outputs = [out] /\ ~not_fresh_at sp out /\
  eval_operand g s = SOME gw /\ eval_operand a s = SOME aw /\
  eval_operand v s = SOME vw /\ eval_operand dp s = SOME ao /\
  eval_operand dl s = SOME az /\ eval_operand rp s = SOME ro /\
  eval_operand rl s = SOME rn /\ step_inst_base inst s = OK u /\
  u.vs_vars = (update_var out word s).vs_vars /\
  u.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE (w2n rn) u.vs_returndata) s).vs_memory /\
  (rn = 0w \/ lo <= w2n ro) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     regions_disjoint (w2n ro) (w2n rn) b sz) /\
  ee.scopes = es.scopes /\ local_ptrs_rel func cenv es.scopes s /\
  local_ptrs_reserved cenv sp /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sp x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sp x) ==>
  !D. ghost_inv_at_mods D lo d cenv cx es G tn s ==>
    ghost_inv_at_mods D lo d cenv cx ee (step_prov PG G inst u)
      (step_taint inst s u tn) (jump_to cont_lbl (next_inst u)) /\
    (step_taint inst s u tn).t_mem = tn.t_mem DIFF
      {j | w2n ro <= j /\ j < w2n ro + LENGTH (TAKE (w2n rn) u.vs_returndata)}
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> gen_tac >> strip_tac >>
  drule_all extcall_dispatch_physical_frame >> strip_tac >>
  `stor_taint_ok_at D tn s` by fs[ghost_inv_at_mods_def] >>
  `stor_taint_ok_at D (step_taint inst s u tn) u` by
    (drule_at (Pat `exec_ext_call _ _ _ _ _ _ _ _ _ _ = _`)
       raw_call_exec_stor_taint_at >>
     disch_then (qspecl_then [`tn`,`D`] mp_tac) >>
     Cases_on `stat` >> simp[]) >>
  `!x. not_fresh_at sp x ==>
    FLOOKUP (step_prov PG G inst u) x = FLOOKUP G x /\
    op_taint (step_taint inst s u tn) (Var x) = op_taint tn (Var x) /\
    lookup_var x u = lookup_var x s` by
    (rpt strip_tac >> `x <> out` by metis_tac[] >>
     simp[step_prov_other_output, step_taint_other_output, update_var_def,
          lookup_var_def, FLOOKUP_UPDATE]) >>
  `new_site_bytes s u = {}` by
    (simp[new_site_bytes_def, FLOOKUP_DEF, EXTENSION] >> metis_tac[]) >>
  conj_asm2_tac
  >- (simp[status_write_ghost_jump] >> irule status_clean_write_ghost_mods >>
      conj_tac >- first_assum ACCEPT_TAC >>
      goal_assum (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `u.vs_memory = (write_memory_with_expansion _ _ _).vs_memory`)) >>
      goal_assum (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
      goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >>
      simp[] >> conj_tac
      >- (rpt strip_tac >>
          qpat_assum `!name b sz. local_region _ _ _ _ _ _ ==> _` drule >>
          simp[regions_disjoint_def, LENGTH_TAKE_EQ] >> IF_CASES_TAC >> decide_tac) >>
      Cases_on `rn = 0w` >> gvs[]) >>
  Cases_on `stat` >>
  simp[step_taint_def, mem_taint_def, step_writes_def, range_bytes_def,
       mem_write_ops_def, memory_range_of_operands_def,
       source_memory_write_ranges_def, written_taint_def, LENGTH_TAKE_EQ,
       EXTENSION, MIN_DEF] >>
  Cases_on `w2n rn < LENGTH u.vs_returndata` >>
  Cases_on `w2n rn <= LENGTH u.vs_returndata` >> simp[] >>
  `w2n rn = LENGTH u.vs_returndata` by decide_tac >> simp[]
QED
