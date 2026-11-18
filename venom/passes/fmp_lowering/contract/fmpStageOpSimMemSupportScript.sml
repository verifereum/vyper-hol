(* Operand and range interfaces for FMP memory simulation. *)
Theory fmpStageOpSimMemSupport
Ancestors
  fmpStagePointRanges[qualified]
  fmpStageOpBase fmpStageRel fmpLowerSequenceExec o1ComposeSupport
  o1PassContract o1LowerDloadAddressArithmetic o1LowerDloadRelocationKernel
  o1LowerDloadJointRelation ptrDiscipline venomState words finite_map pred_set list

Theorem fmp_mem_frontier_bound:
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts ==>
  lo < dimword (:256)
Proof
  MATCH_ACCEPT_TAC fmpStagePointRangesTheory.fmp_mem_frontier_bound
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
  MATCH_ACCEPT_TAC fmpStagePointRangesTheory.fmp_mem_value_clean
QED

Theorem fmp_mem_sites_bounds:
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) ==>
  id = (b,z) /\ 0 < z /\ raw0 <= b /\ fmp0 <= c /\
  b+z < dimword (:256) /\ c+z < dimword (:256)
Proof
  MATCH_ACCEPT_TAC fmpStagePointRangesTheory.fmp_mem_sites_bounds
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
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `wf_function fn` by fs[o1_fn_shape_def] >>
  drule_all fmpStagePointRangesTheory.fmp_mem_operand_range_point >> simp[]
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
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `wf_function fn` by fs[o1_fn_shape_def] >>
  drule_all fmpStagePointRangesTheory.fmp_mem_write_operand_range_point >> simp[]
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
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `wf_function fn` by fs[o1_fn_shape_def] >>
  drule_all fmpStagePointRangesTheory.fmp_mem_read_operand_range_point >> simp[]
QED

Theorem fmp_mem_sites_disjoint:
  fmp_sites_ok sm fmp0 raw0 lo raw /\
  FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
  FLOOKUP (fmp_ld_sites sm) jd = SOME (d,e,w) /\ id <> jd ==>
  (b+z <= d \/ d+w <= b) /\ (c+z <= e \/ e+w <= c)
Proof
  MATCH_ACCEPT_TAC fmpStagePointRangesTheory.fmp_mem_sites_disjoint
QED

Theorem fmp_mem_geometry:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts ==>
  ld_joint_geometry (fmp_ld_sites sm) FEMPTY eom
    (MAP FST (SET_TO_LIST (FDOM (fmp_ld_sites sm))))
Proof
  strip_tac >> drule_all fmp_mem_initial_bounds >> strip_tac >>
  drule_all fmpStagePointRangesTheory.fmp_mem_geometry_point >> simp[]
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
