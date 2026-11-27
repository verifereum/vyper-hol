(* Machine-level linked return-buffer relayout and RET boundary. *)
Theory bodySelectedBufferReturnRunMods
Ancestors
  bodyFullMemoryStore bodyFullIntCallBufferedCopy
  typedCopyOriginPtrBase typedMemoryCopy stmtSimReturn bodyPtrDefs
  fragGasOriginPtr ptrDiscipline venomState

Triviality unlock_frontier:
  (return_unlock_state cenv s).vs_alloca_next = s.vs_alloca_next
Proof
  qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
  Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
  simp[return_unlock_state_def, venomStateTheory.tstore_def,
       venomStateTheory.sstore_def]
QED

Triviality unlock_copy_arrival:
  compile_return_unlock cenv sm = ((),su) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ tn1.t_var = tn.t_var ==>
  let u = return_unlock_state cenv s in
  ~u.vs_halted /\ u.vs_current_bb = su.cs_current_bb /\
  u.vs_inst_idx = LENGTH su.cs_current_insts /\
  u.vs_alloca_next = s.vs_alloca_next /\
  (allocas_below_fmp u <=> allocas_below_fmp s) /\
  (!lo. allocas_from lo u <=> allocas_from lo s) /\
  (!x. lookup_var x u = lookup_var x s) /\
  (!x. op_taint tn1 (Var x) = op_taint tn (Var x)) /\
  (!G x n. ptr_covers G tn1 x u n <=> ptr_covers G tn x s n) /\
  LENGTH (return_unlock_insts cenv sm.cs_next_id) <= LENGTH su.cs_current_insts
Proof
  strip_tac >> drule compile_return_unlock_shape >> strip_tac >>
  qspecl_then [`cenv`, `s`, `sm.cs_next_id`] assume_tac return_unlock_state_frames >>
  simp[unlock_frontier, return_unlock_frames,
       ptrDisciplineTheory.allocas_from_def, lookup_var_def,
       ptr_covers_def, ptrDisciplineTheory.op_taint_def]
QED

(* The copy and RET are one reached machine suffix.  In particular, the
   endpoint is allowed to be in the actual block reached by the copy; no
   same-block assumption is made for the return instruction. *)
Theorem selected_buffer_return_run_mods:
  compile_return_unlock cenv sm = ((),su) /\ fn_has_code sm su func /\
  emit_inst RET [Var rpc] [] sc = ((),sb) /\ fn_has_code sc sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  lookup_var rpc s = SOME pc /\ not_fresh_at su rpc /\
  op_taint tn (Var rpc) = {} /\
  ((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
     ~s.vs_call_ctx.cc_static) /\
  compile_store_memory cenv (Var xs) (Var bp) ty sty su = ((),sc) /\
  ~is_word_type ty /\ fn_inst_ids_distinct func /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fs. FLOOKUP cenv.ce_struct_fields name = SOME fs ==>
    ALL_DISTINCT (MAP FST fs) /\
    EVERY (\(nm,ty,sz). !tv. evaluate_type tenv ty = SOME tv ==>
      sz = type_memory_size tv) fs) /\
  type_widens_to tenv sty ty /\
  (is_bytestring_type ty ==> is_bytestring_type sty) /\
  (~is_bytestring_type ty ==>
    w2n sw + type_memory_size stv <= s.vs_alloca_next /\
    (w2n sw + type_memory_size stv <= w2n bw \/
     w2n bw + type_memory_size tv <= w2n sw)) /\
  evaluate_type tenv sty = SOME stv /\
  evaluate_type tenv ty = SOME tv /\
  0 < type_memory_size stv /\
  type_memory_size stv + 64 < dimword (:256) /\
  type_memory_size stv <= type_memory_size tv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  value_has_type stv v /\ val_wf stv v /\
  value_has_type tv v /\ val_wf tv v /\
  not_fresh_at su xs /\ not_fresh_at su bp /\
  lookup_var xs s = SOME sw /\ lookup_var bp s = SOME bw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  ptr_covers G tn bp s (type_memory_size tv) /\
  s.vs_alloca_next < dimword (:256) /\
  w2n sw + val_store_size stv v < dimword (:256) /\
  w2n bw + type_memory_size tv < dimword (:256) /\
  w2n sw + val_store_size stv v <= s.vs_alloca_next /\
  w2n bw + type_memory_size tv <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code su sc func ==>
  ?r Gf tf copied prev.
    r = IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
      (copied with <|vs_prev_bb := prev; vs_current_bb := sc.cs_current_bb;
                  vs_inst_idx := LENGTH sc.cs_current_insts|>) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (r,Gf,tf)) /\
    val_in_memory tv v (w2n bw) copied.vs_memory /\
    (!mem. mem_agree_outside tf.t_mem copied.vs_memory mem ==>
      val_in_memory tv v (w2n bw) mem) /\
    (copied with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) =
      return_unlock_state cenv s /\
    (!x. not_fresh_at su x ==> lookup_var x copied = lookup_var x s) /\
    (!a len. a + len <= w2n bw \/
      w2n bw + type_memory_size tv <= a ==>
      mem_bytes_at a len copied.vs_memory = mem_bytes_at a len s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH copied.vs_memory /\
    LENGTH (return_unlock_insts cenv sm.cs_next_id) <=
      LENGTH su.cs_current_insts /\
    (((FST cenv.ce_nonreentrant /\
       ~SND (SND (SND cenv.ce_nonreentrant))) ==>
      FST (SND (SND cenv.ce_nonreentrant))) ==>
      tf.t_stor = tn.t_stor /\ tf.t_trans SUBSET tn.t_trans /\
      tf.t_imm = tn.t_imm) /\
    (!i. i < w2n bw ==> (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (SIMP_RULE bool_ss [] return_unlock_origin_ptr_taint) >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  rename1 `tn1.t_var = tn.t_var` >>
  drule_all unlock_copy_arrival >> simp[] >> strip_tac >>
  qabbrev_tac `u = return_unlock_state cenv s` >>
  `?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (u,G,tn1) [] (OK t,Gf,tf)) /\
    val_in_memory tv v (w2n bw) t.vs_memory /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory tv v (w2n bw) mem) /\
    typed_copy_state_frame su (w2n bw) (type_memory_size tv) u t /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts /\
    tf.t_stor = tn1.t_stor /\ tf.t_trans = tn1.t_trans /\ tf.t_imm = tn1.t_imm /\
    (!i. ~(w2n bw <= i /\ i < w2n bw + type_memory_size tv) ==>
      (i IN tf.t_mem <=> i IN tn1.t_mem)) /\
    (!x. not_fresh_at su x ==> lookup_var x t = lookup_var x u /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn1 (Var x))` by
    suspend "copy" >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,Gf,tf) []
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> t,Gf,tf)` by
    suspend "ret" >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> t,Gf,tf)` by
    suspend "join" >>
  qabbrev_tac `copied = t with
    <|vs_prev_bb := u.vs_prev_bb; vs_current_bb := u.vs_current_bb;
      vs_inst_idx := u.vs_inst_idx|>` >>
  qexistsl_tac [`Gf`,`tf`,`copied`,`t.vs_prev_bb`] >>
  suspend "frame"
QED

Resume selected_buffer_return_run_mods[copy]:
  Cases_on `is_bytestring_type ty`
  >- (mp_tac (Q.INST [`sa` |-> `su`, `sb` |-> `sc`, `s` |-> `u`,
        `tn` |-> `tn1`, `xd` |-> `bp`, `dty` |-> `ty`, `dtv` |-> `tv`,
        `dw` |-> `bw`] intcall_widened_bytes_return_copy) >>
      simp[Abbr `u`, return_unlock_frames]) >>
  `w2n sw + type_memory_size stv <= s.vs_alloca_next /\
   (w2n sw + type_memory_size stv <= w2n bw \/
    w2n bw + type_memory_size tv <= w2n sw)` by simp[] >>
  `w2n sw + type_memory_size stv < dimword (:256)` by decide_tac >>
  mp_tac (Q.INST [`sa` |-> `su`, `sb` |-> `sc`, `s` |-> `u`,
    `tn` |-> `tn1`, `xd` |-> `bp`, `dty` |-> `ty`, `dtv` |-> `tv`,
    `dw` |-> `bw`] body_full_memory_store_path) >>
  qpat_assum `!name fields. FLOOKUP cenv.ce_struct_fields name = _ ==> _` mp_tac >>
  simp[Abbr `u`, return_unlock_frames, listTheory.EVERY_MEM, pairTheory.FORALL_PROD] >>
  disch_tac >> disch_then drule >> simp[]
QED

Resume selected_buffer_return_run_mods[ret]:
  `t.vs_allocas = u.vs_allocas` by
    fs[typed_copy_state_frame_def, venom_state_component_equality] >>
  `allocas_below_fmp t <=> allocas_below_fmp u` by
    metis_tac[typed_copy_state_frame_allocas_below_fmp] >>
  `lookup_var rpc t = lookup_var rpc s /\ op_taint tf (Var rpc) = op_taint tn (Var rpc)` by
    (qpat_assum `!x. not_fresh_at su x ==> _` (qspec_then `rpc` mp_tac) >> simp[]) >>
  `allocas_from lo t` by
    (fs[ptrDisciplineTheory.allocas_from_def, Abbr `u`,
        return_unlock_state_frames] >> first_assum ACCEPT_TAC) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t)` by simp[Abbr `u`] >>
  gen_tac >>
  irule (SIMP_RULE list_ss [] (Q.INST [`ops` |-> `[]`] emitted_ret_origin_ptr)) >>
  simp[eval_operands_def] >> qexistsl_tac [`pc`, `rpc`, `sc`, `sb`] >> simp[]
QED

Resume selected_buffer_return_run_mods[join]:
  gen_tac >>
  irule (REWRITE_RULE [listTheory.APPEND] (Q.SPECL
    [`(D,lo,explicit,ctx,func,PG)`,`(s,G,tn)`,`[]`,`(OK u,G,tn1)`]
    gas_origin_ptr_path_append)) >>
  simp[] >> qexistsl_tac [`u`,`tn1`] >> simp[] >>
  irule (REWRITE_RULE [listTheory.APPEND] (Q.SPECL
    [`(D,lo,explicit,ctx,func,PG)`,`(u,G,tn1)`,`[]`,`(OK t,Gf,tf)`]
    gas_origin_ptr_path_append)) >> simp[] >> metis_tac[]
QED

Resume selected_buffer_return_run_mods[frame]:
  `copied with <|vs_prev_bb := t.vs_prev_bb; vs_current_bb := sc.cs_current_bb;
                vs_inst_idx := LENGTH sc.cs_current_insts|> = t` by
    simp[Abbr `copied`, venom_state_component_equality] >>
  `u.vs_vars = s.vs_vars /\ u.vs_memory = s.vs_memory` by simp[Abbr `u`] >>
  fs[typed_copy_state_frame_def, typed_copy_frame_def, Abbr `copied`] >>
  conj_tac
  >- (fs[lookup_var_def] >> rpt strip_tac >>
      qpat_assum `!x. not_fresh_at su x ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
  rpt strip_tac >>
  qpat_assum `!i. _ ==> (i IN tf.t_mem <=> _)` (qspec_then `i` mp_tac) >>
  simp[] >> decide_tac
QED

Finalise selected_buffer_return_run_mods
