Theory bodyFullAbiDecodeOwnedCopy
Ancestors
  bodyFullAbiDecodeLeafCases bodyFullAbiDecodeCopyFrame
  typedCopyOriginPtrDynArray bodyFullGhostFrame abiDecodePtrMemberFrame
  allocaHistory bodyPtrDefs loweringStateRelDefs codegenRel freshWrites stateFrame
  exprLoweringProps emitHelperProps emitHelper compileEnv venomState venomExecSemantics venomInst
  ptrDiscipline ptrSafeRun memSafeRun unitTransformDefs contextCodegenRel memLocDefs
  words arithmetic list rich_list finite_map pred_set pair

(* Identical syntactic owned-state interface; no new logical definition. *)
val owned_decoder_state = ``\st s G tn.
  alloca_history fn s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  abi_decode_ptr_window G tn s input input_word (LENGTH input_bytes) /\
  mem_bytes_at (w2n input_word) (LENGTH input_bytes) s.vs_memory = input_bytes /\
  w2n input_word + LENGTH input_bytes <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas output_id = SOME (output_base,output_cap) /\
  lookup_var output s = SOME (n2w output_base) /\
  ptr_covers G tn output s output_cap /\
  output_base + output_cap < dimword (:256) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < origin.cs_next_id ==> off+sz <= s.vs_alloca_next) /\
  (!name b sz. local_region ce es0.scopes s0 name b sz ==>
      b+sz <= s.vs_alloca_next) /\
  EVERY (\(aid,p,b,k,bytes).
    aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) /\
    lookup_var p s = SOME (n2w b) /\ ptr_covers G tn p s k /\
    op_taint tn (Var p) = {} /\ k = LENGTH bytes /\
    mem_bytes_at b k s.vs_memory = bytes /\ b+k <= s.vs_alloca_next) live /\
  EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) s.vs_memory = bytes) protected /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) /\
  (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [output] /\ inst.inst_id = output_id) /\
  not_local_ptr ce es.scopes output /\ lo <= output_base /\
  (!name b k. local_region ce es.scopes s name b k ==>
    output_base+output_cap <= b \/ b+k <= output_base) /\
  output_id < st.cs_next_id /\ not_fresh_at st output /\
  origin.cs_next_var <= st.cs_next_var /\
  EVERY (\(aid,p,b,k,bytes). not_fresh_at st p) live``;

Theorem abi_decode_owned_mcopy_joint:
  emit_void MCOPY [Var dst;Var src;count_op] sa = ((),sb) /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (^owned_decoder_state) sa s G tn /\ (?H. V H) /\
  local_ptrs_reserved ce sa /\ not_fresh_at sa input /\
  not_fresh_at sa dst /\ not_fresh_at sa src /\
  abi_decoder_operand_live sa.cs_next_var count_op /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  lookup_var dst s = SOME (n2w b) /\ lookup_var src s = SOME (n2w a) /\
  eval_operand count_op s = SOME (n2w n) /\ op_taint tn count_op = {} /\
  ptr_covers G tn dst s n /\ ptr_covers G tn src s n /\
  (!i. a <= i /\ i < a+n ==> i NOTIN tn.t_mem) /\
  a < dimword (:256) /\ b < dimword (:256) /\ n < dimword (:256) /\
  output_base <= b /\ b+n <= output_base+output_cap /\ b+n <= s.vs_alloca_next /\
  a+n <= s.vs_alloca_next /\
  (w2n input_word+LENGTH input_bytes <= b \/ b+n <= w2n input_word) /\
  EVERY (\(aid,p,base,k,bytes). base+k <= b \/ b+n <= base) live /\
  EVERY (\(base,bytes). base+LENGTH bytes <= b \/ b+n <= base) protected ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb t Gf tnf /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  BETA_TAC >> strip_tac >>
  `local_ptrs_rel fn ce es.scopes s` by
    metis_tac[stmt_state_rel_def, state_rel_def] >>
  `eval_operand (Var dst) s = SOME (n2w b) /\
   eval_operand (Var src) s = SOME (n2w a)` by simp[eval_operand_def] >>
  `EVERY (\(aid,p,base,k,bytes).
    FLOOKUP s.vs_allocas aid = SOME (base,k) /\
    lookup_var p s = SOME (n2w base) /\ ptr_covers G tn p s k /\
    op_taint tn (Var p) = {} /\ k = LENGTH bytes /\
    mem_bytes_at base k s.vs_memory = bytes /\ base+k <= s.vs_alloca_next /\
    (base+k <= b \/ b+n <= base)) live` by
    (gvs[EVERY_MEM, FORALL_PROD] >> metis_tac[]) >>
  `EVERY (\(base,bytes). mem_bytes_at base (LENGTH bytes) s.vs_memory = bytes /\
    (base+LENGTH bytes <= b \/ b+n <= base)) protected` by
    (gvs[EVERY_MEM, FORALL_PROD] >> metis_tac[]) >>
  `lo <= b` by decide_tac >>
  mp_tac (abi_decode_mcopy_frame_joint |>
    Q.INST [`dst` |-> `Var dest`, `src` |-> `Var source`] |>
    Q.INST [`dest` |-> `dst`, `source` |-> `src`, `id` |-> `sa.cs_next_id`] |>
    Q.INST [`ob` |-> `output_base`, `cap` |-> `output_cap`, `iw` |-> `input_word`]) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  strip_tac >> rename1 `u = mcopy b a n s` >>
  qabbrev_tac `copy_inst = mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] []` >>
  `emit_inst MCOPY [Var dst;Var src;count_op] [] sa = ((),sb)` by
    gvs[emit_void_def, emit_inst_def] >>
  `step_inst_base copy_inst s = OK u` by
    simp[Abbr `copy_inst`, Once step_inst_base_def, mk_inst_def,
      eval_operand_def, w2n_n2w, LESS_MOD] >>
  `inst_mem_below_frontier copy_inst s /\ inst_dload_in_section copy_inst s` by
    simp[Abbr `copy_inst`, inst_mem_below_frontier_def, inst_dload_in_section_def,
       mk_inst_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
       sized_source_write_range_def, eval_operand_def, w2n_n2w, LESS_MOD] >>
  `allocas_from lo s` by metis_tac[ghost_inv_at_def] >>
  `!D. ptr_inst_ok D lo 0 ctx fn G tn copy_inst s` by
    (gen_tac >>
     `step_inst 0 ctx copy_inst s = OK u` by
       (qpat_x_assum `step_inst_base copy_inst s = _` (SUBST1_TAC o SYM) >>
        simp[step_inst_non_invoke, Abbr `copy_inst`, mk_inst_def]) >>
     `u.vs_requests = s.vs_requests` by simp[mcopy_def, write_memory_with_expansion_def] >>
     gvs[ptr_covers_def] >> simp[ptr_inst_ok_def] >> rpt conj_tac
     >- (simp[Abbr `copy_inst`, access_ok_def, mk_inst_def,
           source_memory_write_ranges_def, fixed_source_write_range_def,
           source_memory_read_ranges_def, sized_source_write_range_def,
           eval_operand_def, mem_write_ops_def, mem_read_ops_def] >>
          rpt strip_tac >> gvs[] >> metis_tac[])
     >- (simp[Abbr `copy_inst`, taint_ok_def, mk_inst_def,
           source_memory_read_ranges_def, sized_source_write_range_def,
           eval_operand_def, w2n_n2w, LESS_MOD] >>
         rpt strip_tac >>
         Cases_on `op = Var dst` >- gvs[] >>
         Cases_on `op = Var src` >- gvs[] >>
         Cases_on `op = count_op` >> gvs[op_taint_def])) >>
  qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (OK t,G',tf)` by
    (gen_tac >>
     mp_tac (Q.INST [`opc` |-> `MCOPY`, `args` |-> `[Var dst;Var src;count_op]`,
       `outs` |-> `[]`, `func` |-> `fn`] typed_copy_emit_inst_origin_ptr_path) >>
     simp[Abbr `t`, Abbr `copy_inst`, is_terminator_def] >> gvs[] >>
     qpat_x_assum `G = step_prov _ _ _ _` (fn th => rewrite_tac[GSYM th])) >>
  drule emit_inst_extends >> strip_tac >>
  drule emitted_insts_emit_inst >> strip_tac >>
  `~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb.cs_current_insts /\ t.vs_allocas = s.vs_allocas` by
    simp[Abbr `t`, mcopy_def, write_memory_with_expansion_def] >>
  `alloca_history fn t` by
    (irule abi_decode_no_alloca_endpoint_history >>
     qexistsl_tac [`s`, `sa`, `sb`] >>
     simp[Abbr `copy_inst`, mk_inst_def, IS_PREFIX_APPEND]) >>
  `!H. V H ==> stmt_state_rel H ctx fn ce cx es t /\
    ghost_inv_at (DF H) lo delta ce cx es G' tf t /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G' tf` by
    (ho_match_mp_tac (abi_decode_scalar_joint_frame |>
       Q.INST [`s` |-> `u`, `G` |-> `G'`, `tn` |-> `tf`]) >>
     simp[Abbr `t`, state_frame_def, lookup_var_def,
       mcopy_def, write_memory_with_expansion_def] >>
     qpat_x_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es u /\ _` mp_tac >>
     simp[mcopy_def, write_memory_with_expansion_def] >> metis_tac[]) >>
  `!p. lookup_var p t = lookup_var p u` by simp[Abbr `t`, lookup_var_def, mcopy_def, write_memory_with_expansion_def] >>
  `!p k. ptr_covers G' tf p t k = ptr_covers G' tf p u k` by
    simp[ptr_covers_def, Abbr `t`, lookup_var_def] >>
  `t.vs_alloca_next = u.vs_alloca_next /\ t.vs_memory = u.vs_memory` by simp[Abbr `t`] >>
  `!name base k. local_region ce es.scopes t name base k =
     local_region ce es.scopes s name base k` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     simp[Abbr `t`, lookup_var_def, mcopy_def, write_memory_with_expansion_def]) >>
  `abi_decode_ptr_window G' tf t input input_word (LENGTH input_bytes)` by
    (gvs[abi_decode_ptr_window_def] >> simp[abi_decode_ptr_window_def] >> metis_tac[]) >>
  qexistsl_tac [`t`, `G'`, `tf`] >> asm_rewrite_tac[] >>
  `!p. not_fresh_at sb p = not_fresh_at sa p` by simp[not_fresh_at_def] >>
  gvs[EVERY_MEM, FORALL_PROD] >>
  (conj_tac >- (rpt gen_tac >> disch_tac >>
    qpat_x_assum `!aid p base k bytes. MEM (aid,p,base,k,bytes) live ==> aid < sa.cs_next_id /\ _` drule >>
    qpat_x_assum `!aid p base k bytes. MEM (aid,p,base,k,bytes) live ==> FLOOKUP s.vs_allocas aid = _ /\ _` drule >>
    simp[] >> rpt strip_tac >> simp[] >> decide_tac) >>
   conj_tac >- (qexists_tac `inst` >> simp[]) >>
   first_assum ACCEPT_TAC)
QED
