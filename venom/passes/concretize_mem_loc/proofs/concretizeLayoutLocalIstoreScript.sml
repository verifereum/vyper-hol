Theory concretizeLayoutLocalIstore
Ancestors concretizeLayoutIstoreProduction concretizeLayoutStateTransport
  concretizeLayoutSupplement
  concretizeLayoutLocalStateWrites frameRelocationCopySteps frameRelocationLocal
  frameRelocationValues frameRelocationGuardedValues frameRelocationEnvironment
  frameRelocationGhostCopy
  concretizeLayoutReaderContext frameRelocationTaintOrder frameRelocationMemory
  ptrDiscipline venomExecSemantics venomState finite_map pred_set list words

Theorem istore_ghost_fields[local]:
  inst.inst_opcode = ISTORE /\ inst.inst_operands = [opd;opv] /\
  inst.inst_outputs = [] /\ eval_operand opd s = SOME dst ==>
  step_prov PG (SND o_f rv) inst post = SND o_f rv /\
  (step_taint inst s (istore (w2n dst) value s) tn).t_var = tn.t_var /\
  (step_taint inst s (istore (w2n dst) value s) tn).t_stor = tn.t_stor /\
  (step_taint inst s (istore (w2n dst) value s) tn).t_trans = tn.t_trans /\
  (step_taint inst s (istore (w2n dst) value s) tn).t_imm =
    key_update tn.t_imm (w2n dst) (op_taint tn opv)
Proof
  strip_tac >>
  simp[step_prov_def, set_prov_def, step_taint_def, out_taint_def,
       set_var_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       fmap_eq_flookup, FLOOKUP_DRESTRICT]
QED

Theorem istore_observation[local]:
  concretize_local_obs s t ==>
  concretize_local_obs (istore k x s) (istore k y t)
Proof
  simp[concretize_local_obs_def, dead_result_rel_def, istore_def,
       mstore_def, write_memory_with_expansion_def,
       imms_agree_except_def, word_agree_except_def]
QED

Theorem istore_supplement[local]:
  concretize_supplement D tn s t /\ word_agree_except m x y ==>
  concretize_supplement D (tn with t_imm := key_update tn.t_imm k m)
    (istore k x s) (istore k y t)
Proof
  strip_tac >> drule_all concretize_supplement_immutables >>
  simp[concretize_supplement_def, istore_def, mstore_def,
       write_memory_with_expansion_def]
QED

Theorem concretize_istore_local_complete:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  ~ctx_has_dalloca C /\ fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  ~joint_read_exempt (EL c (q0::qs)) /\
  o1_fn_shape C fn /\ MEM inst (fn_insts fn) /\
  relocation_env s t /\ relocation_reader_context s t /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn)
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c)
    concretize_local_obs s t /\ concretize_supplement D tn s t /\
  relocation_taint_le
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c) tn un /\
  op_taint un opv SUBSET {k | k < 32} /\
  inst.inst_opcode = ISTORE /\ inst.inst_operands = [opd;opv] /\
  inst.inst_outputs = [] /\
  eval_operand opd s = SOME dst /\ eval_operand opv s = SOME value ==>
  ?tpost. step_inst_base inst t = OK tpost /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn)
        (activation_lookup (0:num) (concretize_positions C')
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
      (guarded_bytes (retpc_var fn) rv (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      concretize_local_obs post tpost /\
    step_prov PG (SND o_f rv) inst post = SND o_f rv /\
    relocation_taint_le
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (step_taint inst s post tn) (step_taint inst t tpost un) /\
    concretize_supplement D (step_taint inst s post tn) post tpost /\
    relocation_env post tpost /\ relocation_reader_context post tpost
Proof
  strip_tac >>
  `s.vs_labels = t.vs_labels` by fs[relocation_env_def] >>
  drule_all concretize_istore_demand_execution >> strip_tac >>
  qexists_tac `istore (w2n dst) valueT t` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "local" >>
  conj_tac >- metis_tac[cj 1 istore_ghost_fields] >>
  conj_tac >- suspend "taint" >>
  conj_tac >- suspend "supplement" >>
  gvs[relocation_env_def, relocation_reader_context_def, istore_def,
      mstore_def, write_memory_with_expansion_def]
QED

Resume concretize_istore_local_complete[local]:
  `concretize_local_obs s t` by metis_tac[local_rel_observation] >>
  `concretize_local_obs post (istore (w2n dst) valueT t)` by
    metis_tac[istore_observation] >>
  `(step_taint inst s post tn).t_var = tn.t_var` by
    metis_tac[cj 2 istore_ghost_fields] >>
  `(guarded_bytes (retpc_var fn) rv (step_taint inst s post tn) : string -> bytes32 -> bytes32 -> bool) =
   guarded_bytes (retpc_var fn) rv tn` by
    (qpat_x_assum `(step_taint inst s post tn).t_var = _` mp_tac >>
     gvs[] >> simp[FUN_EQ_THM, guarded_bytes_def, copy_bytes_def, op_taint_def]) >>
  qpat_x_assum `guarded_bytes _ _ _ = _` (fn th => rewrite_tac[th]) >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`) local_rel_memory_frame >>
  disch_then irule >> conj_tac
  >- simp[istore_def, mstore_def, write_memory_with_expansion_def] >>
  conj_tac >- simp[istore_def, mstore_def, write_memory_with_expansion_def] >>
  conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC
QED

Resume concretize_istore_local_complete[supplement]:
  drule_all istore_supplement >>
  disch_then (qspec_then `w2n dst` assume_tac) >>
  irule concretize_supplement_fields >>
  goal_assum (drule_at (Pat `concretize_supplement _ _ _ _`)) >>
  simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def]
QED

Resume concretize_istore_local_complete[taint]:
  drule_all concretize_istore_demand_geometry >> strip_tac >>
  `demand_taint (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
    (step_taint inst s post tn).t_mem
    (step_taint inst t (istore (w2n dst) valueT t) un).t_mem` by
    (irule demand_taint_istore >> simp[] >>
     qexists_tac `joint_relocation_demand lo (concretize_positions C') q0 es qs c` >>
     simp[] >> metis_tac[]) >>
  `op_taint un opv SUBSET op_taint tn opv` by
    (Cases_on `opv` >> fs[op_taint_def, relocation_taint_le_def]) >>
  pure_rewrite_tac[relocation_taint_le_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       out_taint_def, set_var_taint_def, fmap_eq_flookup, FLOOKUP_DRESTRICT] >>
  fs[relocation_taint_le_def, key_update_def, SUBSET_DEF, op_taint_def,
     FLOOKUP_DRESTRICT] >> rpt strip_tac >> metis_tac[]
QED
Finalise concretize_istore_local_complete
