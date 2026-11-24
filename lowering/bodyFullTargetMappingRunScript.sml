Theory bodyFullTargetMappingRun
Ancestors
  bodyFullMappingSuffixExecution
  bodyFullTargetMappingKey bodyFullTargetMappingScratch targetSubscriptMapping
  exprOperandVar exprSimWordArgs exprSimProps exprSimMapKey
  bodyPtrDefs loweringPosts exprLoweringProps fragGasOriginPtr
  bodyFullUnwrapRun ptrDiscipline loweringStateRelDefs
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  allocaHistory venomState compileEnv finite_map words pred_set list pair fragExec

Theorem mapping_suffix_full_run:
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript bop hashed sp = (slot,sb) /\
  (!x. key = Var x \/ bop = Var x ==> not_fresh_at sn x) /\
  (if is_bytestring_type kt then
     ?x b base cap bs.
       key = Var x /\ eval_operand key s = SOME (n2w b) /\
       FLOOKUP G x = SOME (base,cap) /\ base <= b /\
       b+32+LENGTH bs <= base+cap /\
       b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
       b+32+LENGTH bs <= s.vs_alloca_next /\
       op_taint tn key = {} /\
       (!i. b <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
       mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
       mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
       encode_hashmap_key kt v = word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)
   else eval_operand key s = SOME (encode_hashmap_key kt v) /\
        op_taint tn key = {} /\ op_prov G key = NONE) /\
  eval_operand bop s = SOME base_slot /\ op_taint tn bop = {} /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\ P H0 /\
  (!H. P H ==> stmt_state_rel H ctx func cenv cx es s /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) ==>
  ?t HG tm.
    eval_operand slot t = SOME (hashmap_slot base_slot (encode_hashmap_key kt v)) /\
    op_taint tm slot = {} /\ op_prov HG slot = NONE /\
    (!x. slot = Var x ==> not_fresh_at sb x) /\
    (!x. not_fresh_at sn x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP HG x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv es es sn s t /\ pure_frame cenv func es sn s t /\
    ghost_kept_at lo cenv es sn G tn s HG tm /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ allocas_from lo t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!H. P H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,HG,tm) /\
      stmt_state_rel H ctx func cenv cx es t /\
      ghost_inv_at (DF H) lo d cenv cx es HG tm t)
Proof
  strip_tac >> drule_all mapping_suffix_full_run_with_execution >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`t`, `HG`, `tm`] >> simp[]
QED

(* Apply twice: first to base/index, then to their combined frame and the
   mapping suffix. No effect-free premise is required of the index. *)
Theorem mapping_suffix_frames_join:
  wb_frame cenv es es1 sa s0 s1 /\
  wb_frame cenv es1 es2 sb s1 s2 /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo cenv es1 sb G1 tn1 s1 G2 tn2 /\
  stmt_state_rel H ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id ==>
  wb_frame cenv es es2 sa s0 s2 /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2
Proof
  strip_tac >> conj_tac >- metis_tac[wb_frame_trans] >>
  `local_ptrs_rel func cenv es.scopes s0` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
      lookup_var x s1 = SOME w` by gvs[wb_frame_def] >>
  `!n b sz. local_region cenv es1.scopes s1 n b sz <=>
      local_region cenv es.scopes s0 n b sz` by
    metis_tac[local_region_frame, local_region_frame_fwd] >>
  gvs[ghost_kept_at_def, wb_frame_def] >>
  rpt conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sb x` by
        (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
      qpat_x_assum `!x. not_fresh_at sa x ==> FLOOKUP G1 x = _ /\ _` drule >>
      qpat_x_assum `!x. not_fresh_at sb x ==> FLOOKUP G2 x = _ /\ _` drule >>
      simp[])
  >- (rpt strip_tac >>
      `aid < sb.cs_next_id` by decide_tac >>
      `FLOOKUP s1.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
      `!n b sz'. local_region cenv es1.scopes s1 n b sz' ==>
         off+sz <= b \/ b+sz' <= off` by metis_tac[] >>
      `i IN tn1.t_mem` by
        (qpat_x_assum `!aid off sz i. FLOOKUP s1.vs_allocas aid = _ /\ _ ==> _`
          (qspecl_then [`aid`, `off`, `sz`, `i`] mp_tac) >>
         simp[] >> disch_then irule >> first_assum ACCEPT_TAC) >>
      qpat_x_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
        (qspecl_then [`aid`, `off`, `sz`, `i`] mp_tac) >>
      simp[] >> disch_then irule >> first_assum ACCEPT_TAC)
  >- metis_tac[] >> metis_tac[]
QED
