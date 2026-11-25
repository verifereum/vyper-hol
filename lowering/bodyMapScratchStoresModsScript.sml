(* Linked-state transport at the fixed mapping hash suffix. *)
Theory bodyMapScratchStoresMods
Ancestors
  bodyFullTargetMappingScratch bodyFullTargetMappingScratchTail
  bodyFullUnwrapRun bodyPtrPopTargetSimMapScratchRun
  bodyFullShadowBodyInv bodyFullPostsMods bodyInvSplit
  loweringSlice exprLoweringProps loweringStateRelDefs
  fragGasCopySeqLiftProps fragExecMem memSafeRun unitTransformDefs
  contextCodegenRel codegenRel instMemFrontier
  ptrDiscipline bodyPtrDefs venomState venomExecSemantics venomInst
  words finite_map pred_set list

(* With zero reserved bytes the two ghost predicates have the same
   obligations. Use this only for the horizon-independent frame and the
   shared state relation; the actual pointer path is constructed at lo. *)
Theorem scratch_core_entry[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s ==>
  ghost_inv_at D 0 d cenv cx es G tn s
Proof
  simp[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def] >>
  strip_tac >> asm_rewrite_tac[]
QED

Theorem scratch_linked_ghost[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  ghost_inv_at D 0 d cenv cx es HG tm t /\
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==>
     FLOOKUP HG x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) /\
  mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
  (!i. i IN tm.t_mem ==> i IN tn.t_mem) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  ghost_inv_at_mods D lo d cenv cx es HG tm t
Proof
  strip_tac >> fs[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
    (rpt strip_tac >> `not_fresh_at sa x` by metis_tac[local_ptrs_reserved_def] >>
     gvs[]))
QED

Theorem scratch_linked_immutable[local]:
  immutable_frame_mods func cenv cx es s /\
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  MEM ai (fn_insts func) /\ ai.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas ai.inst_id = SOME (b,64) /\
  (!a n. a+n <= b \/ b+64 <= a ==>
     mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory) /\
  t.vs_data_section = s.vs_data_section /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  immutable_frame_mods func cenv cx es t
Proof
  strip_tac >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def,
     immutable_alloca_sep_mods_def] >> conj_tac
  >- (rpt gen_tac >> disch_tac >>
      irule immutables_rel_mem_agree >> qexists_tac `s` >> simp[] >>
      disch_tac >> rpt gen_tac >> strip_tac >>
      `immutable_alloca_sep func (cenv with ce_module := src) cx es s` by
        (first_x_assum drule >> simp[]) >>
      `regions_disjoint off (type_memory_size tv) b 64` by
        (qpat_x_assum `immutable_alloca_sep _ _ _ _ _`
           (mp_tac o cj 2 o REWRITE_RULE [immutable_alloca_sep_def]) >>
         simp[] >>
         disch_then (qspecl_then [`name`, `tv`, `v`, `off`] mp_tac) >>
         simp[] >> strip_tac >>
         qpat_assum `!inst b sz. _ ==> regions_disjoint _ _ b sz`
           (qspecl_then [`ai`, `b`, `64`] mp_tac) >> simp[]) >>
      first_x_assum irule >> fs[regions_disjoint_def]) >>
  rpt gen_tac >> disch_tac >>
  irule immutable_alloca_sep_fields >> qexistsl_tac [`s`, `es`] >> simp[] >>
  rpt strip_tac >> qexists_tac `id` >>
  `local_region (cenv with ce_module := src) es.scopes t id b' sz <=>
   local_region (cenv with ce_module := src) es.scopes s id b' sz` by
    (irule local_region_lookup_cong >> simp[] >>
     metis_tac[local_ptrs_reserved_def]) >> gvs[]
QED

Theorem scratch_code_mem_ok[local]:
  code = [mk_inst is MSTORE [Var p;bop] [];
          mk_inst ip ADD [Var p;Lit 32w] [q];
          mk_inst ik MSTORE [Var q;key] [];
          mk_inst ih SHA3 [Var p;Lit 64w] [h]] /\
  p <> q /\ (!x. key = Var x ==> x <> q) /\
  eval_operand bop s = SOME w0 /\ eval_operand key s = SOME w1 /\
  lookup_var p s = SOME (n2w b) /\ b+64 < dimword (:256) /\
  b+64 <= s.vs_alloca_next ==> run_inst_seq_mem_ok code s
Proof
  strip_tac >>
  `FLOOKUP s.vs_vars p = SOME (n2w b)` by fs[lookup_var_def] >>
  `b < dimword (:256) /\ b+32 < dimword (:256)` by decide_tac >>
  Cases_on `key` >> fs[eval_operand_def, lookup_var_def] >>
  simp[run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last,
    step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, exec_pure2_def,
    eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  simp[inst_mem_below_frontier_def, source_memory_read_ranges_def,
    source_memory_write_ranges_def, fixed_source_write_range_def,
    memory_range_of_operands_def, eval_operand_def, lookup_var_def] >>
  simp[FLOOKUP_UPDATE, word_add_n2w] >> decide_tac
QED

Theorem scratch_linked_path[local]:
  code = [mk_inst is MSTORE [Var p;bop] [];
          mk_inst ip ADD [Var p;Lit 32w] [q];
          mk_inst ik MSTORE [Var q;key] [];
          mk_inst ih SHA3 [Var p;Lit 64w] [h]] /\
  ALL_DISTINCT [p;q;h] /\ (!x. key = Var x ==> x <> q) /\
  eval_operand bop s = SOME w0 /\ eval_operand key s = SOME w1 /\
  op_taint tn bop = {} /\ op_taint tn key = {} /\
  lookup_var p s = SOME (n2w b) /\ FLOOKUP G p = SOME (root,cap) /\
  root <= b /\ b+64 <= root+cap /\ b+64 < dimword (:256) /\
  b+64 <= s.vs_alloca_next /\ op_taint tn (Var p) = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ code /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ allocas_from lo s /\
  run_inst_seq code s = OK t /\
  HG = DRESTRICT (G |+ (q,(root,cap))) (COMPL {h}) /\
  tm = (tn with <|t_var := tn.t_var |+ (q,{}) |+ (h,{});
       t_mem := (tn.t_mem DIFF {i | b <= i /\ i < b+32})
                      DIFF {i | b+32 <= i /\ i < b+64}|>) ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),HG,tm)
Proof
  strip_tac >>
  `p <> q /\ p <> h /\ q <> h` by fs[ALL_DISTINCT] >>
  drule_all_then assume_tac scratch_code_mem_ok >>
  `!i u. MEM i code ==> dalloca_no_wrap i u` by
    (rpt strip_tac >> irule dalloca_no_wrap_non_dalloca >> gvs[mk_inst_def]) >>
  `!pre i post u. code = pre ++ i::post ==> dalloca_no_wrap i u` by
    metis_tac[MEM_APPEND, MEM] >>
  irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >> simp[] >>
  qexistsl_tac [`code`, `sa`] >>
  simp[mk_inst_def, is_terminator_def] >>
  irule inst_seq_ptr_lower_bound_transport >> simp[] >>
  qexists_tac `0` >> simp[] >>
  irule (SRULE [mk_inst_def] map_scratch_store_hash_checked) >> simp[] >>
  strip_tac >> qpat_assum `!x. key = Var x ==> x <> q`
    (qspec_then `q` mp_tac) >> fs[]
QED

Theorem mapping_scratch_tail_full_run_mods:
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
  op_taint tn (Var p) = {} /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
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
    t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|> = s /\
    (!H. P H ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
          (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),HG,tm) /\
       stmt_state_rel H ctx func cenv cx es
          (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
       immutable_frame_mods func cenv cx es
          (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
       ghost_inv_at_mods (DF H) lo d cenv cx es HG tm
          (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `!H. P H ==> stmt_state_rel H ctx func cenv cx es s /\
               ghost_inv_at (DF H) 0 d cenv cx es G tn s` by
    (gen_tac >> disch_tac >> first_x_assum (drule_then strip_assume_tac) >>
     simp[] >> irule scratch_core_entry >> goal_assum (drule_at Any)) >>
  `allocas_from 0 s` by simp[allocas_from_def] >>
  mp_tac (Q.INST [`lo` |-> `0`] mapping_scratch_tail_full_run) >>
  asm_rewrite_tac[arithmeticTheory.ZERO_LESS_EQ] >> strip_tac >>
  qexistsl_tac [`t`, `HG`, `tm`] >>
  `t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|> = s` by
    (mp_tac mapping_scratch_runtime_restore >> asm_rewrite_tac[]) >>
  `t.vs_data_section = s.vs_data_section` by
    (pop_assum (SUBST1_TAC o SYM) >> simp[]) >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    metis_tac[run_inst_seq_memory_length] >>
  asm_rewrite_tac[] >> qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. P H ==> gas_origin_ptr_path _ _ _ _ /\ _` (drule_then strip_assume_tac) >>
  conj_tac >- (mp_tac (Q.INST
    [`D` |-> `(DF : (bool # 'a word # type_value) list # num list -> dead) H`]
    scratch_linked_path) >>
               asm_rewrite_tac[]) >>
  conj_tac >- asm_rewrite_tac[] >>
  qpat_assum `!H. P H ==> stmt_state_rel _ _ _ _ _ _ _ /\ immutable_frame_mods _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  conj_tac
  >- (irule scratch_linked_immutable >> qexistsl_tac [`ai`, `b`, `s`, `sa`] >>
      simp[lookup_var_def] >> conj_tac
      >- (rpt strip_tac >>
          qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t = _ /\ _`
            (drule_then strip_assume_tac) >> fs[lookup_var_def]) >>
      first_assum ACCEPT_TAC) >>
  qpat_assum `HG = _` (rewrite_tac o single o GSYM) >>
  qpat_assum `tm = _` (rewrite_tac o single o GSYM) >>
  irule scratch_linked_ghost >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G`, `s`, `sa`, `tn`] >> simp[]
QED
