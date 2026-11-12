(* Operand and range interfaces for FMP memory simulation. *)
Theory fmpStageOpSimMemSupport
Ancestors
  fmpStageOpBase fmpStageRel fmpLowerSequenceExec o1ComposeSupport
  o1PassContract o1LowerDloadAddressArithmetic o1LowerDloadRelocationKernel
  o1LowerDloadJointRelation ptrDiscipline venomState words finite_map pred_set list

Theorem fmp_mem_frontier_bound:
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts ==>
  lo < dimword (:256)
Proof
  strip_tac >>
  `fmp_frontier_rel fmp0 raw0 lo s.vs_fmp` by
    fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  drule fmp_frontier_rel_le >>
  strip_tac >> qspec_then `s.vs_fmp` assume_tac w2n_lt >> decide_tac
QED

Theorem fmp_mem_initial_bounds:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp ==>
  eom <= fmp0 /\ fmp0 <= raw0
Proof
  rw[fmp_stage_ctx_def] >>
  `max_live_eom C' = max_live_eom C` by
    (drule ctx_pass_stage_max_live_eom >> EVAL_TAC >> simp[]) >>
  gvs[fmp_variant_room_def]
QED

Theorem fmp_mem_value_clean:
  fmp_value_rel sm NONE {} x y ==> x = y
Proof
  simp[fmp_value_rel_def] >> MATCH_ACCEPT_TAC ld_value_agree_clean
QED

Theorem fmp_mem_sites_bounds:
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) ==>
  id = (b,z) /\ 0 < z /\ raw0 <= b /\ fmp0 <= c /\
  b+z < dimword (:256) /\ c+z < dimword (:256)
Proof
  strip_tac >> Cases_on `id` >>
  gvs[FLOOKUP_fmp_ld_sites, AllCaseEqs()] >>
  `lo < dimword (:256)` by metis_tac[fmp_mem_frontier_bound] >>
  `fmp_sites_ok sm fmp0 raw0 lo s.vs_fmp` by fs[fmp_stage_rel_def] >>
  fs[fmp_sites_ok_def] >>
  qpat_x_assum `!b z c id. FLOOKUP sm (b,z) = SOME (c,id) ==> 0 < z /\ _` drule >> strip_tac >>
  qspec_then `s.vs_fmp` assume_tac w2n_lt >> gvs[]
QED

Theorem fmp_mem_operand_range:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  inst.inst_opcode <> PHI /\ MEM op inst.inst_operands /\
  (!v. op = Var v ==> ~retpc_var fn v) /\
  op_taint tn op = {} /\ eval_operand op s = SOME x /\
  (len <> 0 /\ (eom < w2n x+len \/ op_prov G op <> NONE) ==>
   ?v b z. op = Var v /\ FLOOKUP G v = SOME (b,z) /\
     b <= w2n x /\ w2n x+len <= b+z) ==>
  ?y. eval_operand op t = SOME y /\
    (len=0 \/ (w2n x=w2n y /\ w2n x+len<=eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
       j+len<=z /\ w2n x=b+j /\ w2n y=c+j))
Proof
  strip_tac >>
  `?y. eval_operand op t = SOME y /\
       fmp_value_rel sm (op_prov G op) {} x y` by
    metis_tac[fmp_stage_operand] >>
  qexists_tac `y` >> simp[] >> Cases_on `len=0` >> simp[] >>
  Cases_on `op_prov G op`
  >- (`x=y` by metis_tac[fmp_mem_value_clean] >> gvs[] >>
      Cases_on `eom < w2n x+len` >> gvs[op_prov_def]) >>
  `?v b z. op = Var v /\ FLOOKUP G v = SOME (b,z) /\
     b <= w2n x /\ w2n x+len <= b+z` by metis_tac[optionTheory.NOT_SOME_NONE] >>
  gvs[op_prov_def, fmp_value_rel_def, ld_value_agree_pointer] >>
  drule_all fmp_mem_sites_bounds >> strip_tac >> gvs[] >>
  `b+z < dimword (:256) /\ c+z < dimword (:256)` by
    metis_tac[fmp_mem_sites_bounds] >>
  `w2n (x+n2w c-n2w b) = c+(w2n x-b)` by
    (irule lower_dload_translate_endpoint >> simp[] >>
     qexists_tac `z` >> simp[]) >>
  disj2_tac >> qexistsl_tac [`(b,z)`,`b`,`c`,`z`,`w2n x-b`] >> simp[]
QED

Theorem fmp_mem_write_operand_range:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  inst.inst_opcode <> PHI /\ ~in_revert_forward fn s /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = op /\
  MEM op inst.inst_operands /\ (!v. op = Var v ==> ~retpc_var fn v) /\
  op_taint tn op = {} /\ eval_operand op s = SOME x /\
  MEM (w2n x,len) (source_memory_write_ranges inst s) ==>
  ?y. eval_operand op t = SOME y /\
    (len=0 \/ (w2n x=w2n y /\ w2n x+len<=eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
       j+len<=z /\ w2n x=b+j /\ w2n y=c+j))
Proof
  strip_tac >> irule fmp_mem_operand_range >>
  goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
  `access_ok eom G fn inst s` by metis_tac[fmp_stage_frame_facts] >>
  gvs[access_ok_def] >> metis_tac[]
QED

Theorem fmp_mem_read_operand_range:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  inst.inst_opcode <> PHI /\ ~in_revert_forward fn s /\
  mem_read_ops inst = SOME ops /\ ops.iao_ofst = op /\
  MEM op inst.inst_operands /\ (!v. op = Var v ==> ~retpc_var fn v) /\
  op_taint tn op = {} /\ eval_operand op s = SOME x /\
  MEM (w2n x,len) (source_memory_read_ranges inst s) ==>
  ?y. eval_operand op t = SOME y /\
    (len=0 \/ (w2n x=w2n y /\ w2n x+len<=eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
       j+len<=z /\ w2n x=b+j /\ w2n y=c+j))
Proof
  strip_tac >> irule fmp_mem_operand_range >>
  goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
  `access_ok eom G fn inst s` by metis_tac[fmp_stage_frame_facts] >>
  gvs[access_ok_def] >> metis_tac[]
QED

Theorem fmp_mem_sites_disjoint:
  fmp_sites_ok sm fmp0 raw0 lo raw /\
  FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
  FLOOKUP (fmp_ld_sites sm) jd = SOME (d,e,w) /\ id <> jd ==>
  (b+z <= d \/ d+w <= b) /\ (c+z <= e \/ e+w <= c)
Proof
  Cases_on `id` >> Cases_on `jd` >>
  gvs[FLOOKUP_fmp_ld_sites, AllCaseEqs(), fmp_sites_ok_def] >>
  metis_tac[]
QED

Theorem fmp_mem_geometry:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts ==>
  ld_joint_geometry (fmp_ld_sites sm) FEMPTY eom
    (MAP FST (SET_TO_LIST (FDOM (fmp_ld_sites sm))))
Proof
  strip_tac >>
  `eom <= fmp0 /\ fmp0 <= raw0` by metis_tac[fmp_mem_initial_bounds] >>
  simp[ld_joint_geometry_def] >> rpt conj_tac
  >- (rpt strip_tac >> simp[MEM_MAP] >> metis_tac[MEM_SET_TO_LIST, FDOM_FINITE])
  >- (rpt strip_tac >> drule_all fmp_mem_sites_bounds >> strip_tac >> simp[]) >>
  rpt strip_tac >>
  `fmp_sites_ok sm fmp0 raw0 lo s.vs_fmp` by fs[fmp_stage_rel_def] >>
  drule_all fmp_mem_sites_disjoint >> simp[]
QED

Theorem fmp_mem_operand_clean:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  inst.inst_opcode <> PHI /\ MEM op inst.inst_operands /\
  (!v. op = Var v ==> ~retpc_var fn v) /\
  op_prov G op = NONE /\ op_taint tn op = {} /\
  eval_operand op s = SOME x ==>
  eval_operand op t = SOME x
Proof
  metis_tac[fmp_stage_operand, fmp_mem_value_clean]
QED
