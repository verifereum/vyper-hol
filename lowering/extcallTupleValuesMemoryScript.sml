(* Concrete captured values through the actual argument-tuple stores. *)
Theory extcallTupleValuesMemory
Ancestors
  extcallCaptureStoreFrameMemory extcallCaptureValueMemory
  extcallSingleNonwordStoreMemory extcallSingleWordStoreMemory extcallStoreStagesMemory
  extcallTupleStoreMemory exprSimIfExpWidenedAdapter
  abiBytestringAllocation externalEntryShape freshWrites venomMemDefs venomState
  exprLoweringProps fragGasPathMem fragExec exprSimMemDefs exprSimCopy
  exprSimVVFrame exprSimProps bodyMemAssignAttrStorage
  abiEncoderWordSource abiTupleProps localValueStoreProps valueLoadProps
  valueEncodingProofs valueEncoding valueEncodingDefs loweringPosts exprLowering compileEnv context vyperState
  loweringStateRelDefs list words

Theorem captured_memory_cell_frame[local]:
  vv_holds ce cx ty (Value v) (LocatedValue tag p) es s /\
  vv_at ce cx ty sa sb es (Value v) (LocatedValue tag p) s /\
  p.ptr_location = LocMemory /\ ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
  eval_operand p.ptr_operand t = eval_operand p.ptr_operand s /\
  sb.cs_next_id <= limit /\
  (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ aid < limit ==>
    mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory) /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
    mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory) ==>
  vv_holds ce cx ty (Value v) (LocatedValue tag p) es t
Proof
  strip_tac >>
  `?w. eval_operand p.ptr_operand s = SOME w /\
       val_in_memory tv v (w2n w) s.vs_memory` by
    (gvs[vv_holds_def,read_result_def,return_def] >> metis_tac[]) >>
  `mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory =
   mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory` by
    (drule_all extcall_captured_registered_memory_frame >> simp[]) >>
  `val_in_memory tv v (w2n w) t.vs_memory` by
    (irule val_in_memory_footprint_agree >> conj_tac
     >- first_assum ACCEPT_TAC >> qexists_tac `s.vs_memory` >> simp[]) >>
  fs[vv_holds_def,read_result_def,return_def] >> metis_tac[]
QED

Theorem captured_tuple_compiler_split[local]:
  compile_extcall_store_values ce ((vv,lt)::vals) buf off sa = ((),sb) /\
  fn_has_code sa sb func ==>
  ?cell_end. compile_extcall_store_values ce [(vv,lt)] buf off sa = ((),cell_end) /\
    compile_extcall_store_values ce vals buf (off+type_memory_bytes ce lt) cell_end = ((),sb) /\
    ci_mono sa cell_end /\
    fn_has_code sa cell_end func /\ fn_has_code cell_end sb func
Proof
  strip_tac >>
  qpat_x_assum `compile_extcall_store_values _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_extcall_store_values_def,comp_bind_def,
       comp_ignore_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> simp[comp_bind_def,comp_ignore_bind_def,comp_return_def]) >>
  strip_tac >> gvs[] >>
  rename1 `compile_extcall_store_values ce vals buf _ sm = ((),sb)` >>
  `compile_extcall_store_values ce [(vv,lt)] buf off sa = ((),sm)` by
    simp[compile_extcall_store_values_def,comp_bind_def,
         comp_ignore_bind_def,comp_return_def] >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    (qspecl_then [`ce`,`[(vv,lt)]`,`buf`,`off`,`sa`]
       mp_tac compile_extcall_store_values_labels >>
     qspecl_then [`ce`,`vals`,`buf`,`off+type_memory_bytes ce lt`,`sm`]
       mp_tac compile_extcall_store_values_labels >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_mid,cs_extends_refl] >>
  drule_all extcall_single_store_stages >> strip_tac >>
  qexists_tac `sm` >> simp[] >> metis_tac[ci_mono_trans]
QED

Theorem captured_word_encoding:
  vv_holds ce cx ty (Value v) (StackValue tag op) es s /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v ==>
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\
  abi_tuple_word tv v /\ type_memory_size tv = 32
Proof
  strip_tac >>
  `type_memory_size tv = 32` by metis_tac[evaluated_word_memory_size] >>
  `eval_operand op s = SOME (typed_val_to_w256 tv v)` by
    gvs[vv_holds_def,expr_val_rel_def,read_result_def,return_def] >>
  simp[] >> Cases_on `ty` >> gvs[is_word_type_def]
  >- (drule evaluate_type_base_identity >> strip_tac >> gvs[] >>
      irule abi_encoder_base_word_value >> simp[is_word_type_def]) >>
  gvs[vyperValueTheory.evaluate_type_def,AllCaseEqs(),
      vyperTypingTheory.value_has_type_def,abi_tuple_word_def] >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]
QED

Theorem captured_old_allocations_frame[local]:
  alloca_inv s /\ FLOOKUP s.vs_allocas did = SOME (b,bytes) /\
  limit <= did /\ did < sa.cs_next_id /\ off+write_size <= bytes /\
  (!aid a n x k. FLOOKUP s.vs_allocas aid = SOME (a,n) /\
    aid < sa.cs_next_id /\ a <= x /\ x+k <= a+n /\
    (x+k <= b+off \/ b+off+write_size <= x) ==>
    mem_bytes_at x k t.vs_memory = mem_bytes_at x k s.vs_memory) ==>
  !aid a n. FLOOKUP s.vs_allocas aid = SOME (a,n) /\ aid < limit ==>
    mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `allocas_non_overlapping s /\ aid <> did /\ aid < sa.cs_next_id` by
    (fs[alloca_inv_def] >> decide_tac) >>
  `a+n <= b+off \/ b+off+write_size <= a` by
    (qspecl_then [`s`,`aid`,`did`,`a`,`n`,`b`,`bytes`,
                  `a`,`n`,`b+off`,`write_size`] mp_tac allocated_windows_disjoint >>
     (impl_tac >- (simp[] >> decide_tac)) >> simp[]) >>
  qpat_x_assum `!aid a n x k. _`
    (qspecl_then [`aid`,`a`,`n`,`a`,`n`] mp_tac) >> simp[]
QED

Theorem captured_nonword_cell_frame[local]:
  vv_holds ce cx ty (Value v) vv es s /\
  vv_at ce cx ty sa sb es (Value v) vv s /\ ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  contract_storage t = contract_storage s /\ contract_transient t = contract_transient s /\
  sb.cs_next_id <= limit /\
  (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ aid < limit ==>
    mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory) /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
    mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory) ==>
  vv_holds ce cx ty (Value v) vv es t
Proof
  strip_tac >> Cases_on `vv`
  >- (rename1 `StackValue tag op` >>
      `vv_holds ce cx ty (Value v) (LocatedValue ty (mk_ptr op LocMemory)) es s` by
        (fs[vv_holds_def,expr_val_rel_def,read_result_def,return_def] >>
         simp[vv_holds_def,mk_ptr_def,read_result_def,return_def] >> metis_tac[]) >>
      `vv_at ce cx ty sa sb es (Value v) (LocatedValue ty (mk_ptr op LocMemory)) s` by
        (fs[vv_at_def,expr_val_at_def,read_result_def,return_def] >>
         simp[vv_at_def,mk_ptr_def,read_result_def,return_def,local_place_at_def] >>
         metis_tac[]) >>
      `vv_holds ce cx ty (Value v) (LocatedValue ty (mk_ptr op LocMemory)) es t` by
        (mp_tac (Q.INST [`tag` |-> `ty`, `p` |-> `mk_ptr op LocMemory`]
          (SPEC_ALL captured_memory_cell_frame)) >>
         (impl_tac >- (fs[mk_ptr_def,vv_operand_def] >> metis_tac[])) >> simp[]) >>
      fs[vv_holds_def,mk_ptr_def,expr_val_rel_def,read_result_def,return_def] >>
      metis_tac[]) >>
  rename1 `LocatedValue tag p` >> Cases_on `p.ptr_location = LocMemory`
  >- (mp_tac (SPEC_ALL captured_memory_cell_frame) >>
      (impl_tac >- (fs[vv_operand_def] >> metis_tac[])) >> simp[]) >>
  Cases_on `p.ptr_location` >>
  gvs[vv_holds_def,vv_operand_def,storage_holds_def,immutable_holds_def] >>
  metis_tac[]
QED

Theorem captured_cell_frame:
  vv_holds ce cx ty (Value v) vv es s /\
  vv_at ce cx ty sa sb es (Value v) vv s /\
  vv_store_bound cx ty ty es (Value v) vv s /\ vv_storage_live cx vv es s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
  (is_word_type ty ==> ?tag op. vv = StackValue tag op) /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  contract_storage t = contract_storage s /\ contract_transient t = contract_transient s /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry) /\
  (!name b sz. local_region ce es.scopes t name b sz <=>
    local_region ce es.scopes s name b sz) /\
  (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ aid < sb.cs_next_id ==>
    mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory) /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
    mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory) ==>
  vv_holds ce cx ty (Value v) vv es t /\
  vv_at ce cx ty sa sb es (Value v) vv t /\
  vv_store_bound cx ty ty es (Value v) vv t /\ vv_storage_live cx vv es t
Proof
  strip_tac >> conj_tac
  >- (Cases_on `is_word_type ty`
      >- (`?tag op. vv = StackValue tag op` by metis_tac[] >>
          gvs[vv_holds_def,vv_operand_def,expr_val_rel_def,
              read_result_def,return_def] >> metis_tac[]) >>
      mp_tac (Q.INST [`limit` |-> `sb.cs_next_id`]
        (SPEC_ALL captured_nonword_cell_frame)) >>
      (impl_tac >- (simp[arithmeticTheory.ADD_ASSOC] >> metis_tac[])) >> simp[]) >>
  conj_tac
  >- (irule vv_at_alloc_mono_frame >> qexistsl_tac [`s`,`sb`] >> simp[]) >>
  conj_tac
  >- (irule vv_store_bound_frame_mem_src >> qexists_tac `s` >> simp[]) >>
  Cases_on `vv` >> fs[vv_operand_def] >> metis_tac[]
QED

Theorem captured_cell_store_mem[local]:
  compile_extcall_store_values ce [(vv,lt)] buf off sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  stmt_state_rel ctx func ce cx es s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand buf s = SOME (n2w b) /\
  b+off+type_memory_size tv < dimword (:256) /\
  b+off+type_memory_size tv <= s.vs_alloca_next /\
  evaluate_type (get_tenv cx) lt = SOME tv /\
  type_memory_bytes ce lt = type_memory_size tv /\
  0 < type_memory_size tv /\ value_has_type tv v /\ val_wf tv v /\
  vv_holds ce cx lt (Value v) vv es s /\
  vv_store_bound cx lt lt es (Value v) vv s /\ vv_storage_live cx vv es s /\
  (is_word_type lt ==> ?tag op. vv = StackValue tag op) /\
  (!x. vv_operand vv = Var x \/ buf = Var x ==> not_fresh_at sa x) /\
  (!tag p. vv = LocatedValue tag p ==>
    (p.ptr_location <> LocMemory \/ is_word_type tag ==> tag = lt) /\
    (p.ptr_location = LocCode /\ ce.ce_is_ctor ==>
      !region. ce.ce_imm_alloca = SOME region ==>
        eval_operand region s = SOME 0w /\
        (!x. region = Var x ==> not_fresh_at sa x))) /\
  (!name a n. local_region ce es.scopes s name a n ==>
    a+n <= b+off \/ b+off+type_memory_size tv <= a) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size tv)) ==>
  ?z. gas_path_mem ctx func s 0 (OK z) /\
    stmt_state_rel ctx func ce cx es z /\ alloca_history func z /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory tv v (b+off) z.vs_memory /\
    contract_storage z = contract_storage s /\
    contract_transient z = contract_transient s /\
    z.vs_data_section = s.vs_data_section /\ z.vs_labels = s.vs_labels /\
    s.vs_alloca_next <= z.vs_alloca_next /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP z.vs_allocas aid = SOME entry) /\
    (!aid a n x k. FLOOKUP s.vs_allocas aid = SOME (a,n) /\
      aid < sa.cs_next_id /\ a <= x /\ x+k <= a+n /\
      (x+k <= b+off \/ b+off+type_memory_size tv <= x) ==>
      mem_bytes_at x k z.vs_memory = mem_bytes_at x k s.vs_memory) /\
    (!name a n x k. local_region ce es.scopes s name a n /\
      a <= x /\ x+k <= a+n ==>
      mem_bytes_at x k z.vs_memory = mem_bytes_at x k s.vs_memory) /\
    (!name io itv iv x k. ce.ce_is_ctor /\
      FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) /\
      io <= x /\ x+k <= io+type_memory_size itv ==>
      mem_bytes_at x k z.vs_memory = mem_bytes_at x k s.vs_memory)
Proof
  strip_tac >> reverse (Cases_on `is_word_type lt`)
  >- (`is_bytestring_type lt \/ type_memory_bytes ce lt <> 0` by decide_tac >>
      mp_tac (SPEC_ALL extcall_single_nonword_store_mem) >>
      (impl_tac >- asm_rewrite_tac[]) >> simp[]) >>
  `?tag op. vv = StackValue tag op` by metis_tac[] >> gvs[] >>
  drule_all captured_word_encoding >> strip_tac >>
  mp_tac (Q.INST [`tv` |-> `tv`, `v` |-> `v`, `ty` |-> `lt`]
    extcall_single_word_store_mem) >>
  (impl_tac >- (fs[vv_operand_def] >> metis_tac[])) >> strip_tac >>
  qexists_tac `z` >> simp[] >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!a k. _ ==> mem_bytes_at a k z.vs_memory = _` irule >>
      decide_tac)
  >- (rpt strip_tac >>
      `a+n <= b+off \/ b+off+32 <= a` by
        (qpat_x_assum `!name a n. local_region ce es.scopes s name a n ==> _`
           (qspecl_then [`name`,`a`,`n`] mp_tac) >> simp[]) >>
      qpat_x_assum `!a k. _ ==> mem_bytes_at a k z.vs_memory = _` irule >>
      decide_tac)
  >> (rpt strip_tac >>
      `regions_disjoint io (type_memory_size itv) (b+off) 32` by
        (qpat_x_assum `ce.ce_is_ctor ==> !name itv iv io. _`
          (mp_tac o Q.SPECL [`name`,`itv`,`iv`,`io`] o UNDISCH) >> simp[]) >>
      qpat_x_assum `!a k. _ ==> mem_bytes_at a k z.vs_memory = _` irule >>
      qpat_x_assum `regions_disjoint _ _ _ _` mp_tac >>
      simp[regions_disjoint_def] >> decide_tac)
QED

Theorem captured_tuple_store_mem:
  !cells sa sb off s.
  compile_extcall_store_values ce (MAP FST cells) buf off sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  stmt_state_rel ctx func ce cx es s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand buf s = SOME (n2w b) /\
  (!x. buf = Var x ==> not_fresh_at sa x) /\
  FLOOKUP s.vs_allocas did = SOME (b,bytes) /\
  cap_end.cs_next_id <= did /\ did < sa.cs_next_id /\
  off + SUM (MAP (type_memory_size o FST o SND) cells) <= bytes /\
  b+bytes < dimword (:256) /\
  (!name a n. local_region ce es.scopes s name a n ==>
    a+n <= b \/ b+bytes <= a) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) b bytes) /\
  EVERY (\((vv,lt),(tv,v)).
    evaluate_type (get_tenv cx) lt = SOME tv /\
    type_memory_bytes ce lt = type_memory_size tv /\
    0 < type_memory_size tv /\ value_has_type tv v /\ val_wf tv v /\
    vv_holds ce cx lt (Value v) vv es s /\
    vv_at ce cx lt cap_start cap_end es (Value v) vv s /\
    vv_store_bound cx lt lt es (Value v) vv s /\ vv_storage_live cx vv es s /\
    (is_word_type lt ==> ?tag op. vv = StackValue tag op) /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
    (!tag p. vv = LocatedValue tag p ==>
      (p.ptr_location <> LocMemory \/ is_word_type tag ==> tag = lt) /\
      (p.ptr_location = LocCode /\ ce.ce_is_ctor ==>
        !region. ce.ce_imm_alloca = SOME region ==>
          eval_operand region s = SOME 0w /\
          (!x. region = Var x ==> not_fresh_at sa x)))) cells ==>
  ?z. gas_path_mem ctx func s 0 (OK z) /\
    stmt_state_rel ctx func ce cx es z /\ alloca_history func z /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tuple_in_memory (MAP (SND o SND) cells) (MAP (FST o SND) cells)
      (b+off) z.vs_memory /\
    contract_storage z = contract_storage s /\
    contract_transient z = contract_transient s /\
    z.vs_data_section = s.vs_data_section /\ z.vs_labels = s.vs_labels /\
    s.vs_alloca_next <= z.vs_alloca_next /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP z.vs_allocas aid = SOME entry) /\
    (!aid a n x k. FLOOKUP s.vs_allocas aid = SOME (a,n) /\
      aid < sa.cs_next_id /\ a <= x /\ x+k <= a+n /\
      (x+k <= b+off \/
       b+off+SUM (MAP (type_memory_size o FST o SND) cells) <= x) ==>
      mem_bytes_at x k z.vs_memory = mem_bytes_at x k s.vs_memory) /\
    (!name a n x k. local_region ce es.scopes s name a n /\
      a <= x /\ x+k <= a+n ==>
      mem_bytes_at x k z.vs_memory = mem_bytes_at x k s.vs_memory) /\
    (!name io itv iv x k. ce.ce_is_ctor /\
      FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) /\
      io <= x /\ x+k <= io+type_memory_size itv ==>
      mem_bytes_at x k z.vs_memory = mem_bytes_at x k s.vs_memory)
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      gvs[compile_extcall_store_values_def,comp_return_def] >>
      qexists_tac `s` >> simp[cj 1 gas_path_mem_rules,val_in_memory_def]) >>
  rpt gen_tac >> strip_tac >> PairCases_on `h` >> fs[] >>
  rename1 `vv_holds ce cx lt (Value v) vv es s` >>
  rename1 `evaluate_type (get_tenv cx) lt = SOME tv` >>
  drule_all captured_tuple_compiler_split >> strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `!x. vv_operand vv = Var x \/ buf = Var x ==> not_fresh_at sa x` by
    metis_tac[] >>
  `b+off+type_memory_size tv < dimword (:256) /\
   b+off+type_memory_size tv <= s.vs_alloca_next` by
    (fs[alloca_inv_def,alloca_next_valid_def] >>
     first_x_assum (qspec_then `did` mp_tac) >> simp[] >> decide_tac) >>
  `!name a n. local_region ce es.scopes s name a n ==>
    a+n <= b+off \/ b+off+type_memory_size tv <= a` by
    (rpt strip_tac >> first_x_assum drule >> decide_tac) >>
  `ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size tv)` by
    (rpt strip_tac >>
     `regions_disjoint io (type_memory_size itv) b bytes` by metis_tac[] >>
     fs[regions_disjoint_def] >> decide_tac) >>
  mp_tac (Q.INST [`sb` |-> `cell_end`] (SPEC_ALL captured_cell_store_mem)) >>
  (impl_tac >- (asm_simp_tac bool_ss [] >> rpt conj_tac >>
               first_assum ACCEPT_TAC)) >> strip_tac >>
  rename1 `gas_path_mem ctx func s 0 (OK mid)` >>
  suspend "captures"
QED
Resume captured_tuple_store_mem[captures]:
  markerLib.RESUME_TAC >>
  `!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
    eval_operand op mid = eval_operand op s` by
    (rpt strip_tac >> Cases_on `op` >> fs[eval_operand_def] >> metis_tac[]) >>
  `!name a n. local_region ce es.scopes mid name a n <=>
    local_region ce es.scopes s name a n` by
    metis_tac[copy_buffer_local_region_frame] >>
  `!aid a n. FLOOKUP s.vs_allocas aid = SOME (a,n) /\ aid < cap_end.cs_next_id ==>
    mem_bytes_at a n mid.vs_memory = mem_bytes_at a n s.vs_memory` by
    (`off+type_memory_size tv <= bytes` by decide_tac >>
     mp_tac (Q.INST [`did` |-> `did`, `b` |-> `b`, `bytes` |-> `bytes`,
                    `off` |-> `off`, `write_size` |-> `type_memory_size tv`,
                    `sa` |-> `sa`, `t` |-> `mid`, `limit` |-> `cap_end.cs_next_id`]
       (SPEC_ALL captured_old_allocations_frame)) >>
     (impl_tac >- (pure_asm_rewrite_tac [] >> simp_tac bool_ss [] >> rpt conj_tac >>
                  first_assum ACCEPT_TAC)) >> simp[]) >>
  `!name a n. local_region ce es.scopes s name a n ==>
    mem_bytes_at a n mid.vs_memory = mem_bytes_at a n s.vs_memory` by
    (rpt strip_tac >>
     qpat_x_assum `!name a n x k. local_region ce es.scopes s _ _ _ /\ _ ==> _`
       (qspecl_then [`name`,`a`,`n`,`a`,`n`] mp_tac) >> simp[]) >>
  qpat_x_assum `!sa sb off s. _`
    (qspecl_then [`cell_end`,`sb`,`off+type_memory_size tv`,`mid`] mp_tac) >>
  (impl_tac >- suspend "tail_pre") >>
  strip_tac >> suspend "join"
QED
Resume captured_tuple_store_mem[tail_pre]:
  markerLib.RESUME_TAC >>
  `local_ptrs_reserved ce cell_end` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `did < cell_end.cs_next_id` by (fs[ci_mono_def] >> decide_tac) >>
  `!x. buf = Var x ==> not_fresh_at cell_end x` by
    (rpt strip_tac >> irule not_fresh_at_mono >>
     qexists_tac `sa` >> fs[ci_mono_def]) >>
  `eval_operand buf mid = SOME (n2w b)` by metis_tac[] >>
  qmatch_goalsub_abbrev_tac `EVERY remaining cells` >>
  `EVERY remaining cells` by
    (simp[Abbr`remaining`,EVERY_MEM] >> rpt strip_tac >> PairCases_on `e` >>
      rename1 `MEM ((cvv,cty),(ctv,cv)) cells` >>
      qpat_x_assum `EVERY _ cells` (mp_tac o REWRITE_RULE[EVERY_MEM]) >>
      disch_then (qspec_then `((cvv,cty),(ctv,cv))` mp_tac) >>
      simp[] >> strip_tac >>
      `eval_operand (vv_operand cvv) mid = eval_operand (vv_operand cvv) s` by
        metis_tac[] >>
      mp_tac (Q.INST [`ty` |-> `cty`, `vv` |-> `cvv`,
                         `tv` |-> `ctv`, `v` |-> `cv`,
                         `sa` |-> `cap_start`, `sb` |-> `cap_end`, `t` |-> `mid`]
        (SPEC_ALL captured_cell_frame)) >>
      (impl_tac >- (pure_asm_rewrite_tac [] >> simp_tac bool_ss [] >>
                   rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
      simp[] >> fs[ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
  pure_asm_rewrite_tac [] >> simp_tac bool_ss [] >> rpt conj_tac
  >- (qpat_x_assum `compile_extcall_store_values ce (MAP FST cells) _ _ cell_end = _`
        mp_tac >> asm_simp_tac bool_ss [])
  >- metis_tac[] >> suspend "tail_rest"
QED
Resume captured_tuple_store_mem[tail_rest]:
  markerLib.RESUME_TAC >> decide_tac
QED
Resume captured_tuple_store_mem[join]:
  markerLib.RESUME_TAC >>
  `gas_path_mem ctx func s 0 (OK z)` by
    (drule_all gas_path_mem_then >> simp[]) >>
  `mem_bytes_at (b+off) (val_footprint tv v) z.vs_memory =
   mem_bytes_at (b+off) (val_footprint tv v) mid.vs_memory` by
    (`val_footprint tv v <= type_memory_size tv` by
       metis_tac[val_footprint_le] >>
     qpat_x_assum `!aid a n x k. FLOOKUP mid.vs_allocas _ = _ /\ _ ==> _`
       (qspecl_then [`did`,`b`,`bytes`,`b+off`,`val_footprint tv v`] mp_tac) >>
     simp[] >> fs[ci_mono_def] >> decide_tac) >>
  `val_in_memory tv v (b+off) z.vs_memory` by
    (irule val_in_memory_footprint_agree >> simp[] >>
     qexists_tac `mid.vs_memory` >> simp[]) >>
  qexists_tac `z` >> simp[Once val_in_memory_def] >>
  rpt conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at cell_end x` by (fs[ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
      metis_tac[])
  >- suspend "registered"
  >- (rpt strip_tac >>
      `local_region ce es.scopes mid name a n` by metis_tac[] >>
      qpat_x_assum `!name a n x k. local_region ce es.scopes mid _ _ _ /\ _ ==> _`
        (qspecl_then [`name`,`a`,`n`,`x`,`k`] mp_tac) >>
      qpat_x_assum `!name a n x k. local_region ce es.scopes s _ _ _ /\ _ ==> _`
        (qspecl_then [`name`,`a`,`n`,`x`,`k`] mp_tac) >> simp[])
  >- (rpt strip_tac >>
      qpat_x_assum `!name io itv iv x k. _`
        (qspecl_then [`name`,`io`,`itv`,`iv`,`x`,`k`] mp_tac) >>
      qpat_x_assum `!name io itv iv x k. _`
        (qspecl_then [`name`,`io`,`itv`,`iv`,`x`,`k`] mp_tac) >> simp[]) >>
  decide_tac
QED
Resume captured_tuple_store_mem[registered]:
  markerLib.RESUME_TAC >>
  rpt strip_tac >>
  `FLOOKUP mid.vs_allocas aid = SOME (a,n) /\ aid < cell_end.cs_next_id` by
    (fs[ci_mono_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  `x+k <= b+off \/ b+off+type_memory_size tv <= x` by decide_tac >>
  `x+k <= b+(off+type_memory_size tv) \/
   b+(off+type_memory_size tv)+SUM (MAP (type_memory_size o FST o SND) cells) <= x` by
    decide_tac >>
  qpat_x_assum `!aid a n x k. FLOOKUP mid.vs_allocas _ = _ /\ _ ==> _`
    (qspecl_then [`aid`,`a`,`n`,`x`,`k`] mp_tac) >>
  qpat_x_assum `!aid a n x k. FLOOKUP s.vs_allocas _ = _ /\ _ ==> _`
    (qspecl_then [`aid`,`a`,`n`,`x`,`k`] mp_tac) >> simp[]
QED
Finalise captured_tuple_store_mem
