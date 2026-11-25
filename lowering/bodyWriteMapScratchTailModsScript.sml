(* The counted mapping scratch suffix at the original allocation floor. *)
Theory bodyWriteMapScratchTailMods
Ancestors
  bodyFullTargetMappingScratchTail bodyFullTargetMappingScratch
  bodyFullShadowBodyInv bodyFullPostsMods bodyInvSplit loweringSlice
  bodyPtrPopTargetSimMapScratchRun bodyFullUnwrapRun
  fragGasCopySeqLiftProps fragGasCopyLoop fragGasOriginPtr fragExecMem
  exprLoweringProps ptrDiscipline bodyPtrDefs loweringStateRelDefs
  venomState venomInst venomExecSemantics fragExec finite_map pred_set list words
  unitTransformDefs contextCodegenRel codegenRel venomMemDefs instMemFrontier

(* Floor zero is used for the ordinary semantic post only. The path is
   separately certified at the real floor, on the same raw result. *)
Theorem linked_scratch_ordinary_ghost[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s ==>
  ghost_inv_at D 0 d cenv cx es G tn s
Proof
  rewrite_tac[ghost_inv_at_mods_def, ghost_inv_at_def] >>
  strip_tac >> asm_rewrite_tac[] >> simp[allocas_from_def]
QED

Theorem linked_scratch_restore_ghost[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  ghost_inv_at D 0 d cenv cx es HG tm t /\
  mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
  tm.t_mem SUBSET tn.t_mem /\ t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next /\ local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> FLOOKUP HG x = FLOOKUP G x /\
                            op_taint tm (Var x) = op_taint tn (Var x)) ==>
  ghost_inv_at_mods D lo d cenv cx es HG tm t
Proof
  simp[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def,
       SUBSET_DEF, local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem linked_scratch_restore_immutable[local]:
  immutable_frame_mods func cenv cx es s /\
  MEM ai (fn_insts func) /\ ai.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas ai.inst_id = SOME (b,64) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_data_section = s.vs_data_section /\ LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!a n. a+n <= b \/ b+64 <= a ==>
     mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory) ==>
  immutable_frame_mods func cenv cx es t
Proof
  strip_tac >>
  `!src id a n. local_region (cenv with ce_module := src) es.scopes t id a n <=>
                 local_region (cenv with ce_module := src) es.scopes s id a n` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     simp[local_ptrs_reserved_def] >> fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def, immutable_alloca_sep_mods_def] >>
  reverse conj_tac
  >- (rpt strip_tac >> irule immutable_alloca_sep_fields >>
      qexistsl_tac [`s`,`es`] >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> irule immutables_rel_mem_agree >> qexists_tac `s` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >>
  `immutable_alloca_sep func (cenv with ce_module := src) cx es s` by metis_tac[] >>
  fs[immutable_alloca_sep_def] >>
  qpat_assum `cenv.ce_is_ctor ==> !name tv v off. _` mp_tac >> simp[] >>
  disch_then (drule_all_then strip_assume_tac) >>
  first_x_assum (qspecl_then [`ai`,`b`,`64`] mp_tac) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def]
QED

Theorem linked_scratch_memory_checks[local]:
  ALL_DISTINCT [p;q;h] /\ (!x. key = Var x ==> x <> q) /\
  eval_operand bop s = SOME w0 /\ eval_operand key s = SOME w1 /\
  lookup_var p s = SOME (n2w b) /\
  b+64 < dimword (:256) /\ b+64 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok
    [mk_inst is MSTORE [Var p;bop] []; mk_inst ip ADD [Var p;Lit 32w] [q];
     mk_inst ik MSTORE [Var q;key] []; mk_inst ih SHA3 [Var p;Lit 64w] [h]] s
Proof
  strip_tac >>
  `b < dimword (:256) /\ b+32 < dimword (:256)` by decide_tac >>
  Cases_on `key` >> fs[ALL_DISTINCT, eval_operand_def, lookup_var_def] >>
  simp[run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last,
       step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  simp[inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, fixed_source_write_range_def,
       memory_range_of_operands_def, eval_operand_def, lookup_var_def] >>
  simp[FLOOKUP_UPDATE, word_add_n2w] >> decide_tac
QED

Theorem mapping_scratch_tail_run_mods:
  code = [mk_inst is MSTORE [Var p;bop] [];
          mk_inst ip ADD [Var p;Lit 32w] [q];
          mk_inst ik MSTORE [Var q;key] [];
          mk_inst ih SHA3 [Var p;Lit 64w] [h]] /\
  ALL_DISTINCT [p;q;h] /\ (!x. key = Var x ==> x <> q) /\
  eval_operand bop s = SOME w0 /\ eval_operand key s = SOME w1 /\
  op_taint tn bop = {} /\ op_taint tn key = {} /\
  lookup_var p s = SOME (n2w b) /\ FLOOKUP G p = SOME (root,cap) /\
  root <= b /\ b+64 <= root+cap /\ lo <= b /\
  b+64 < dimword (:256) /\ b+64 <= s.vs_alloca_next /\
  op_taint tn (Var p) = {} /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!x. not_fresh_at sa x ==> x <> q /\ x <> h) /\
  local_ptrs_reserved cenv sa /\
  MEM ai (fn_insts func) /\ ai.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas ai.inst_id = SOME (b,64) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!name a n. local_region cenv es.scopes s name a n ==> a+n <= b \/ b+64 <= a) /\
  fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ code /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (!H. P H ==> stmt_state_rel H ctx func cenv cx es s /\
                immutable_frame_mods func cenv cx es s /\
                ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) ==>
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
       stmt_state_rel H ctx func cenv cx es (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
       immutable_frame_mods func cenv cx es (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
       ghost_inv_at_mods (DF H) lo d cenv cx es HG tm
          (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `!H. P H ==> stmt_state_rel H ctx func cenv cx es s /\
                ghost_inv_at (DF H) 0 d cenv cx es G tn s` by
    (gen_tac >> disch_tac >> first_x_assum (drule_then strip_assume_tac) >>
     simp[] >> irule linked_scratch_ordinary_ghost >> goal_assum (drule_at Any)) >>
  `allocas_from 0 s` by simp[allocas_from_def] >>
  mp_tac (Q.INST [`lo` |-> `0`] mapping_scratch_tail_full_run) >>
  (impl_tac >- (simp[] >> (metis_tac[]))) >> strip_tac >>
  rename1 `run_inst_seq code s = OK t` >>
  qexistsl_tac [`t`,`HG`,`tm`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (rename1 `!a n. _ ==> mem_bytes_at a n _ = _` >> metis_tac[]) >>
  suspend "finish"
QED

Resume mapping_scratch_tail_run_mods[finish]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. P H ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then (strip_assume_tac o CONJUNCT2)) >>
  qpat_assum `!H. P H ==> stmt_state_rel H _ _ _ _ _ s /\ immutable_frame_mods _ _ _ _ s /\ _`
    (drule_then strip_assume_tac) >>
  conj_tac >- suspend "real_path" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "immutables" >>
  suspend "ghost"
QED

Resume mapping_scratch_tail_run_mods[real_path]:
  `!i u. MEM i code ==> unitTransformDefs$dalloca_no_wrap i u` by
    (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     gvs[mk_inst_def]) >>
  `!pre i post u. code = pre ++ i::post ==> unitTransformDefs$dalloca_no_wrap i u` by
    metis_tac[MEM_APPEND, MEM] >>
  irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >>
  simp[] >> qexistsl_tac [`code`, `sa`] >> simp[] >>
  conj_tac >- simp[mk_inst_def, is_terminator_def] >>
  conj_tac
  >- (irule linked_scratch_memory_checks >> rpt conj_tac >>
      TRY (first_assum ACCEPT_TAC) >>
      FIRST [qexists_tac `w0` >> first_assum ACCEPT_TAC,
             qexists_tac `w1` >> first_assum ACCEPT_TAC,
             qexists_tac `b` >> rpt conj_tac >> first_assum ACCEPT_TAC]) >>
  irule fragGasCopySeqLiftPropsTheory.inst_seq_ptr_lower_bound_transport >>
  simp[mk_inst_def] >> qexists_tac `0` >> simp[] >>
  gvs[ALL_DISTINCT] >>
  irule (SRULE [mk_inst_def] map_scratch_store_hash_checked) >> simp[]
QED

Resume mapping_scratch_tail_run_mods[immutables]:
  `t.vs_data_section = s.vs_data_section` by
    (drule_all mapping_scratch_runtime_restore >>
     disch_then (mp_tac o AP_TERM ``venom_state_vs_data_section``) >> simp[]) >>
  drule run_inst_seq_memory_length >> strip_tac >>
  irule linked_scratch_restore_immutable >>
  qexistsl_tac [`ai`,`b`,`s`,`sa`] >> simp[] >>
  conj_tac
  >- (simp[lookup_var_def] >> rpt strip_tac >>
      qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t = _ /\ _`
        (drule_then (assume_tac o REWRITE_RULE [lookup_var_def] o CONJUNCT1)) >>
      first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Resume mapping_scratch_tail_run_mods[ghost]:
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (qpat_assum `!a n. _ ==> mem_bytes_at a n t.vs_memory = _`
       (qspecl_then [`0`,`lo`] mp_tac) >> simp[]) >>
  `tm.t_mem SUBSET tn.t_mem` by
    (qpat_assum `tm = _` (SUBST1_TAC) >> simp[SUBSET_DEF]) >>
  irule linked_scratch_restore_ghost >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G`,`s`,`sa`,`tn`] >> simp[] >>
  rpt strip_tac >>
  qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t = _ /\ _`
    (drule_then (strip_assume_tac o CONJUNCT2)) >>
  first_assum ACCEPT_TAC
QED

Finalise mapping_scratch_tail_run_mods
