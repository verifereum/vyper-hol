(* The Sim-named dependency supplies only fixed-instruction execution checks,
   not a target simulation judgment. *)
Theory bodyFullTargetMappingScratchTail
Ancestors
  bodyPtrPopTargetSimMapScratchRun bodyFullUnwrapSlotPost bodyFullUnwrapRun
  bodyFullAllocGeneric fragGasCopyLoop fragExecMem instMemFrontier
  valueEncodingProps exprSimMapKey exprSimPrecompiles exprSimHash fragExec exprLoweringProps vyperStorage
  bodyPtrDefs ptrDiscipline venomState venomExecSemantics venomInst
  words finite_map pred_set list

Theorem mapping_scratch_tail_full_run:
  code = [mk_inst is MSTORE [Var p;bop] [];
          mk_inst ip ADD [Var p;Lit 32w] [q];
          mk_inst ik MSTORE [Var q;key] [];
          mk_inst ih SHA3 [Var p;Lit 64w] [h]] /\
  ALL_DISTINCT [p;q;h] /\
  (!x. key = Var x ==> x <> q) /\
  eval_operand bop s = SOME w0 /\ eval_operand key s = SOME w1 /\
  op_taint tn bop = {} /\ op_taint tn key = {} /\
  lookup_var p s = SOME (n2w b) /\ FLOOKUP G p = SOME (root,cap) /\
  root <= b /\ b+64 <= root+cap /\ lo <= b /\
  b+64 < dimword (:256) /\ b+64 <= s.vs_alloca_next /\
  op_taint tn (Var p) = {} /\ ~ctx_has_dalloca ctx /\
  (!x. not_fresh_at sa x ==> x <> q /\ x <> h) /\
  local_ptrs_reserved cenv sa /\
  MEM ai (fn_insts func) /\ ai.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas ai.inst_id = SOME (b,64) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!name a n. local_region cenv es.scopes s name a n ==>
     a+n <= b \/ b+64 <= a) /\
  fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ code /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (!H. P H ==> stmt_state_rel H ctx func cenv cx es s /\
                 ghost_inv_at (DF H) lo d cenv cx es G tn s) ==>
  ?t HG tm.
    run_inst_seq code s = OK t /\
    eval_operand (Var h) t = SOME (hashmap_slot w0 w1) /\
    HG = DRESTRICT (G |+ (q,(root,cap))) (COMPL {h}) /\
    tm = (tn with <|t_var := tn.t_var |+ (q,{}) |+ (h,{});
       t_mem := (tn.t_mem DIFF {i | b <= i /\ i < b+32})
                      DIFF {i | b+32 <= i /\ i < b+64}|>) /\
    op_taint tm (Var h) = {} /\ op_prov HG (Var h) = NONE /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP HG x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) /\
    (!a n. a+n <= b \/ b+64 <= a ==>
       mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!H. P H ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
          (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),HG,tm) /\
       stmt_state_rel H ctx func cenv cx es
          (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
       ghost_inv_at (DF H) lo d cenv cx es HG tm
          (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  qabbrev_tac `z = mstore (b+32) w1
       (update_var q (n2w (b+32)) (mstore b w0 s))` >>
  qabbrev_tac `t = update_var h (hashmap_slot w0 w1) z` >>
  qabbrev_tac `HG = DRESTRICT (G |+ (q,(root,cap))) (COMPL {h})` >>
  qabbrev_tac `tm = tn with <|t_var := tn.t_var |+ (q,{}) |+ (h,{});
       t_mem := (tn.t_mem DIFF {i | b <= i /\ i < b+32})
                      DIFF {i | b+32 <= i /\ i < b+64}|>` >>
  qexistsl_tac [`t`, `HG`, `tm`] >>
  conj_asm1_tac >- suspend "execution" >>
  conj_tac >- simp[Abbr `t`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[Abbr `HG`] >> conj_tac >- simp[Abbr `tm`] >>
  conj_tac >- simp[Abbr `tm`, op_taint_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[Abbr `HG`, op_prov_def, FLOOKUP_DRESTRICT] >>
  conj_asm1_tac >- suspend "registers" >>
  conj_asm1_tac >- suspend "memory" >>
  conj_tac >- simp[Abbr `t`, Abbr `z`, update_var_def, mstore_def] >>
  conj_tac >- simp[Abbr `t`, Abbr `z`, update_var_def, mstore_def] >>
  qx_gen_tac `H` >> strip_tac >> first_x_assum drule >> strip_tac >>
  conj_asm1_tac >- suspend "path" >>
  conj_asm1_tac >- suspend "state" >> suspend "ghost"
QED

Resume mapping_scratch_tail_full_run[execution]:
  `b < dimword (:256) /\ b+32 < dimword (:256)` by decide_tac >>
  `p <> q /\ p <> h /\ q <> h` by gvs[ALL_DISTINCT] >>
  `mem_bytes_at b 64 z.vs_memory = word_to_bytes w0 T ++ word_to_bytes w1 T` by
    (`mem_bytes_at b 32 (update_var q (n2w (b+32)) (mstore b w0 s)).vs_memory =
        word_to_bytes w0 T` by simp[update_var_def, mem_bytes_at_mstore_same] >>
     drule mem_bytes_at_store_append >>
     disch_then (qspec_then `w1` mp_tac) >> simp[Abbr `z`]) >>
  `step_inst_base (mk_inst ih SHA3 [Var p;Lit 64w] [h]) z = OK t` by
    (simp[Abbr `t`, hashmap_slot_def, byteTheory.word_of_bytes_be_def] >>
     irule step_SHA3_bytes >>
     qexistsl_tac [`64w`, `n2w b`] >>
     conj_tac >- simp[byteTheory.word_to_bytes_be_def] >>
     simp[eval_operand_def, Abbr `z`, lookup_var_def, update_var_def,
          mstore_def, FLOOKUP_UPDATE] >> gvs[lookup_var_def]) >>
  `step_inst_base (mk_inst is MSTORE [Var p;bop] []) s = OK (mstore b w0 s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, eval_operand_def] >>
  `step_inst_base (mk_inst ip ADD [Var p;Lit 32w] [q]) (mstore b w0 s) =
     OK (update_var q (n2w (b+32)) (mstore b w0 s))` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def,
       lookup_var_def, mstore_def, word_add_n2w] >> gvs[lookup_var_def]) >>
  `eval_operand key (update_var q (n2w (b+32)) (mstore b w0 s)) = SOME w1` by
    (qpat_x_assum `eval_operand key s = _` mp_tac >>
     qpat_x_assum `!x. key = _ ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `key` >>
     simp[eval_operand_def, lookup_var_def, mstore_def, update_var_def, FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `step_inst_base (mk_inst ik MSTORE [Var q;key] [])
     (update_var q (n2w (b+32)) (mstore b w0 s)) = OK z` by
    (simp[Abbr `z`, step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def] >>
     simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  simp[run_inst_seq_def]
QED
Resume mapping_scratch_tail_full_run[registers]:
  rpt strip_tac >> `x <> q /\ x <> h` by metis_tac[] >>
  simp[Abbr `t`, Abbr `z`, Abbr `HG`, Abbr `tm`, lookup_var_def,
       update_var_def, mstore_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def]
QED
Resume mapping_scratch_tail_full_run[memory]:
  rpt strip_tac >>
  simp[Abbr `t`, Abbr `z`, update_var_def] >>
  irule EQ_TRANS >>
  irule_at Any mstore_mem_bytes_at_disjoint >>
  simp[] >>
  irule mstore_mem_bytes_at_disjoint >> decide_tac
QED
Resume mapping_scratch_tail_full_run[path]:
  irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >>
  simp[] >> qexistsl_tac [`code`, `sa`] >> simp[] >>
  conj_tac >- (simp[mk_inst_def, is_terminator_def]) >>
  conj_tac >- suspend "memchecks" >>
  simp[Abbr `HG`, Abbr `tm`] >>
  irule fragGasCopyLoopTheory.inst_seq_ptr_lower_bound_transport >>
  simp[mk_inst_def] >> qexists_tac `0` >> simp[] >>
  gvs[ALL_DISTINCT] >>
  irule (SRULE [mk_inst_def] map_scratch_store_hash_checked) >> simp[]
QED
Resume mapping_scratch_tail_full_run[state]:
  `not_local_ptr cenv es.scopes q /\ not_local_ptr cenv es.scopes h` by
    (gvs[loweringStateRelDefsTheory.local_ptrs_reserved_def, loweringStateRelDefsTheory.not_local_ptr_def] >> metis_tac[]) >>
  simp[stmt_state_rel_inst_idx, Abbr `t`] >>
  irule stmt_state_rel_update_var >> simp[] >>
  simp[Abbr `z`] >> irule exprSimAllocTheory.literal_mstore_state_rel >>
  conj_tac >- (qexistsl_tac [`b`, `ai`, `64`] >>
     simp[update_var_def, mstore_def] >> suspend "localframe") >>
  irule stmt_state_rel_update_var >> simp[] >>
  irule exprSimAllocTheory.literal_mstore_state_rel >>
  simp[] >> qexistsl_tac [`b`, `ai`, `64`] >> simp[] >> metis_tac[]
QED
Resume mapping_scratch_tail_full_run[ghost]:
  irule unwrap_slot_copy_ghost_inv_at >>
  conj_tac >- simp[Abbr `t`, Abbr `z`, update_var_def, mstore_def] >>
  conj_tac >- (simp[allocas_from_def, Abbr `t`, Abbr `z`, update_var_def, mstore_def] >>
     metis_tac[allocas_from_def]) >>
  conj_tac >- (qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
     qpat_x_assum `stor_taint_ok_at _ _ _` mp_tac >>
     simp[Abbr `tm`] >>
     simp[Abbr `t`] >> simp[Abbr `z`] >>
     simp_tac (srw_ss()) [stor_taint_ok_at_def, update_var_def, mstore_def, LET_THM]) >>
  qexistsl_tac [`G`, `func`, `64`, `s`, `sa`, `b`, `tn`] >>
  simp[lookup_var_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[lookup_var_def] >>
  conj_tac >- (rpt strip_tac >> simp[Abbr `tm`] >> decide_tac) >>
  gvs[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def] >>
  rpt strip_tac >> simp[Abbr `tm`] >> decide_tac
QED
Resume mapping_scratch_tail_full_run[memchecks]:
  `FLOOKUP s.vs_vars p = SOME (n2w b)` by gvs[lookup_var_def] >>
  `p <> q /\ b < dimword (:256) /\ b+32 < dimword (:256)` by
    (gvs[ALL_DISTINCT] >> decide_tac) >>
  Cases_on `key` >> fs[eval_operand_def, lookup_var_def] >>
  simp[run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last,
    step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, exec_pure2_def,
    eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
    contextCodegenRelTheory.source_memory_read_ranges_def,
    codegenRelTheory.source_memory_write_ranges_def,
    codegenRelTheory.fixed_source_write_range_def,
    contextCodegenRelTheory.memory_range_of_operands_def,
    eval_operand_def, lookup_var_def] >>
  simp[FLOOKUP_UPDATE, word_add_n2w] >> decide_tac
QED
Resume mapping_scratch_tail_full_run[localframe]:
  rpt strip_tac >>
  `local_region cenv es.scopes s name lb lsz` by
    (qpat_x_assum `local_region _ _ _ _ _ _` mp_tac >>
     simp[loweringStateRelDefsTheory.local_region_def, lookup_var_def, FLOOKUP_UPDATE] >>
     gvs[loweringStateRelDefsTheory.not_local_ptr_def] >> metis_tac[]) >>
  metis_tac[]
QED
Finalise mapping_scratch_tail_full_run
