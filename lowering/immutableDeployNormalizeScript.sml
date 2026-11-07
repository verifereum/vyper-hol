Theory immutableDeployNormalize
Ancestors
  immutableDeployOperandTransfer placeStoreDynPrepare placeStoreAllocPath
  placeTypedCopyRecursivePath exprSimBufferStore exprLoweringProps compileEnv
  typedMemoryCopy venomState stmtLowering exprLowering finite_map loweringHalt
  freshWrites fragGasMode fragExec venomInst exprSimAlloc valueEncodingProps
  exprSimFieldLayout vyperTypeSystem

(* The normalizing arm cannot have a bytestring destination: widening into
   a bytestring already has a bytestring source, bypassing normalization. *)
Theorem immutable_normalized_copy_size:
  type_widens_to tenv sty dty /\
  ~(is_bytestring_type dty /\ is_bytestring_type sty) /\
  mem_size = type_memory_size dtv ==>
  (if is_bytestring_type dty then type_memory_bytes cenv sty else mem_size) =
    32 * ((type_memory_size dtv + 31) DIV 32)
Proof
  strip_tac >>
  `~is_bytestring_type dty` by
    (Cases_on `dty` >> gvs[is_bytestring_type_def] >>
     Cases_on `b` >> gvs[is_bytestring_type_def] >>
     Cases_on `sty` >> gvs[type_widens_to_def, arg_type_fits_def,
       is_bytestring_type_def] >>
     Cases_on `b` >> gvs[arg_type_fits_def, is_bytestring_type_def] >>
     rename1 `arg_type_fits (BaseT (BytesT sbound)) (BaseT (BytesT dbound))` >>
     Cases_on `sbound` >> Cases_on `dbound` >>
     gvs[arg_type_fits_def, is_bytestring_type_def]) >>
  simp[slot_count_of_memory_size, cj 1 type_memory_size_slots]
QED

Theorem immutable_normalized_composite_path:
  compile_alloc_buffer (type_memory_size dtv) sa = (buf,mid) /\
  compile_store_memory_typed cenv buf.buf_operand dty src sty mid = ((),sm) /\
  compile_imm_store_words (SOME region) buf.buf_operand dst n 0 sm = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  stmt_state_rel ctx func cenv cx es s /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  type_memory_size dtv < dimword (:256) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid ==>
     w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  cenv.ce_imm_alloca = SOME region /\
  (!x. region = Var x ==> not_fresh_at sa x) /\
  eval_operand region s = SOME 0w /\ cenv.ce_is_ctor /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  cenv.ce_module_var_type (cenv.ce_module,id) = SOME dty /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  dw = n2w off /\ L = type_memory_size dtv /\ L = 32*n /\
  off+L < dimword (:256) ==>
  ?r q pw.
    gas_marked_path F ctx func s 0 (OK r) /\
    stmt_state_rel ctx func cenv cx es r /\
    eval_operand buf.buf_operand r = SOME pw /\
    eval_operand dst r = SOME (n2w off) /\ eval_operand region r = SOME 0w /\
    val_in_memory dtv v (w2n pw) r.vs_memory /\
    w2n pw+L < dimword (:256) /\ regions_disjoint (w2n pw) L off L /\
    gas_marked_path F ctx func r 0 (OK q) /\
    gas_marked_path F ctx func s 0 (OK q) /\
    mem_bytes_at off L q.vs_memory = mem_bytes_at (w2n pw) L r.vs_memory /\
    (!a k. regions_disjoint a k off L ==>
       mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s) /\
    (!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x r) /\
    (q with <|vs_vars := r.vs_vars; vs_memory := r.vs_memory;
              vs_immutables := r.vs_immutables; vs_prev_bb := r.vs_prev_bb;
              vs_current_bb := r.vs_current_bb; vs_inst_idx := r.vs_inst_idx|>) = r /\
    q.vs_immutables =
      (immutable_transfers T T pw (n2w off) n 0 r).vs_immutables /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `cs_extends sa mid` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends mid sm` by
    metis_tac[cj 1 ci_mono_typed_memory_family, ci_mono_def, pairTheory.SND] >>
  `cs_extends sm sb` by metis_tac[ci_mono_compile_imm_store_words, ci_mono_def, pairTheory.SND] >>
  `fn_has_code sa mid func /\ fn_has_code mid sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  drule_all place_alloc_buffer_source_path >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `w2n sw + type_memory_size stv <= w2n w \/
   w2n w + type_memory_size dtv <= w2n sw` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ u` kall_tac >>
     irule place_alloca_source_disjoint >> simp[] >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     qexistsl_tac [
       `mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_size dtv))]
         [STRING #"%" (toString sa.cs_next_var)]`,
       `STRING #"%" (toString sa.cs_next_var)`, `raw`] >>
     gvs[run_inst_seq_def, mk_inst_def, venomExecSemanticsTheory.step_inst_base_def,
         venomStateTheory.eval_operands_def,
         venomStateTheory.eval_operand_def, lookup_var_def, AllCaseEqs()] >>
     rpt strip_tac >>
     qpat_x_assum `!aid b sz. _ /\ sa.cs_next_id <= aid ==> _` drule >> simp[]) >>
  qpat_x_assum `run_inst_seq _ _ = _` kall_tac >>
  qpat_x_assum `u = raw with vs_inst_idx := _` kall_tac >>
  `eval_operand src u = SOME sw /\ eval_operand dst u = SOME dw /\
   eval_operand region u = SOME 0w` by
    (conj_tac >- (Cases_on `src` >> gvs[venomStateTheory.eval_operand_def]) >>
     conj_tac >- (Cases_on `dst` >> gvs[venomStateTheory.eval_operand_def]) >>
     Cases_on `region` >> gvs[venomStateTheory.eval_operand_def]) >>
  `(!x. src = Var x ==> not_fresh_at mid x) /\
   (!x. dst = Var x ==> not_fresh_at mid x) /\
   (!x. region = Var x ==> not_fresh_at mid x) /\
   (!x. buf.buf_operand = Var x ==> not_fresh_at mid x)` by
    (simp[] >> rpt conj_tac >> rpt strip_tac >>
     qpat_x_assum `!y. not_fresh_at sa y ==> not_fresh_at mid y` irule >>
     first_x_assum irule >> simp[]) >>
  `local_ptrs_reserved cenv mid` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `val_in_memory stv v (w2n sw) u.vs_memory` by simp[] >>
  drule compile_store_memory_typed_forward_run >>
  disch_then (qspec_then `tenv` mp_tac) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ u.vs_memory`)) >>
  disch_then (drule_at (Pat `fn_has_code mid sm _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ dty = _`)) >>
  disch_then (drule_at (Pat `eval_operand buf.buf_operand u = _`)) >>
  disch_then (qspec_then `ctx` mp_tac) >>
  simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  (drule_all buffer_alloc_code >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es t` by
    (irule place_typed_copy_alloca_state_frame >>
     goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
     qexistsl_tac [`type_memory_size dtv`,
       `mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_size dtv))]
         [STRING #"%" (toString sa.cs_next_var)]`] >>
     simp[mk_inst_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (irule (gas_marked_path_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SIMP_RULE (srw_ss()) []) >>
     qexists_tac `u` >> simp[gas_marked_path_def]) >>
  `eval_operand buf.buf_operand t = SOME w /\
   eval_operand dst t = SOME dw /\ eval_operand region t = SOME 0w` by
    (conj_tac >-
       (drule typed_copy_state_frame_operand >>
        disch_then (qspec_then `buf.buf_operand` mp_tac) >> simp[]) >>
     conj_tac >-
       (drule typed_copy_state_frame_operand >>
        disch_then (qspec_then `dst` mp_tac) >> simp[]) >>
     drule typed_copy_state_frame_operand >>
     disch_then (qspec_then `region` mp_tac) >> simp[]) >>
  `t.vs_allocas = u.vs_allocas` by
    (qpat_assum `typed_copy_state_frame _ _ _ _ _`
       (strip_assume_tac o SRULE [typed_copy_state_frame_def,
          venom_state_component_equality]) >> simp[]) >>
  `regions_disjoint (w2n w) L off L` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ t`
       (strip_assume_tac o REWRITE_RULE[stmt_state_rel_def]) >>
     qpat_x_assum `immutable_alloca_sep _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE[immutable_alloca_sep_def]) >>
     qpat_x_assum `immutable_decl_sep _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE[immutable_decl_sep_def]) >>
     simp[] >> disch_then (qspecl_then [`id`,`dty`,`dtv`,`off`] mp_tac) >>
     simp[] >> strip_tac >>
     qpat_x_assum `!aid b sz. FLOOKUP u.vs_allocas aid = _ ==> _`
       (qspec_then `sa.cs_next_id` mp_tac) >>
     simp[regions_disjoint_def] >> decide_tac) >>
  `mid.cs_next_var <= sm.cs_next_var` by
    metis_tac[cj 1 ci_mono_typed_memory_family, ci_mono_def, pairTheory.SND] >>
  `(!x. dst = Var x ==> not_fresh_at sm x) /\
   (!x. region = Var x ==> not_fresh_at sm x) /\
   (!x. buf.buf_operand = Var x ==> not_fresh_at sm x)` by
    (rpt conj_tac >> rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `mid` >> simp[]) >>
  `eval_operand buf.buf_operand t = SOME (n2w (w2n w))` by simp[] >>
  drule_at (Pat `compile_imm_store_words _ _ _ _ _ _ = _`)
    immutable_words_old_prefix_path >>
  disch_then (qspec_then `t` mp_tac) >>
  disch_then (drule_at (Pat `eval_operand buf.buf_operand t = _`)) >>
  disch_then (qspecl_then [`L`,`func`,`ctx`,`off`] mp_tac) >>
  simp[regions_disjoint_def] >>
  (impl_tac >- (fs[regions_disjoint_def] >> decide_tac)) >> strip_tac >>
  `gas_marked_path F ctx func s 0
     (OK (u' with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule (gas_marked_path_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SIMP_RULE (srw_ss()) []) >>
     qexists_tac `t` >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    (rpt strip_tac >>
     qpat_assum `typed_copy_state_frame _ _ _ _ _`
       (strip_assume_tac o SRULE [typed_copy_state_frame_def]) >>
     `not_fresh_at mid x` by simp[] >>
     qpat_x_assum `!x. not_fresh_at mid x ==> _` drule >> simp[]) >>
  qpat_assum `u' with <|vs_memory := _; vs_vars := _; vs_immutables := _|> = t`
    (strip_assume_tac o SRULE [venom_state_component_equality]) >>
  qexistsl_tac [`t`,`u' with vs_inst_idx := LENGTH sb.cs_current_insts`,`w`] >>
  fs[venom_state_component_equality, regions_disjoint_def,
       lookup_var_def, same_blocks_def, venomStateTheory.eval_operand_def] >>
  (conj_tac >-
    (qpat_x_assum `eval_operand buf.buf_operand t = SOME w` mp_tac >>
     gvs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]) >>
  qpat_x_assum `32 * n = type_memory_size dtv` (fn th =>
    rule_assum_tac (REWRITE_RULE [th])) >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `!a k. _ \/ _ ==> _`
    (qspecl_then [`a`,`k`] mp_tac) >>
  simp[arithmeticTheory.ADD_COMM]))

QED
