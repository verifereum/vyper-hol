(* Current-state identity cases of captured external-call argument unwrap. *)
Theory extcallUnwrapIdentityMemory
Ancestors
  exprSimMemUnwrap exprSimMemDefs loweringPosts fragGasPathMem
  exprLowering compileEnv exprSimConvert valueEncodingProps venomState words list

Theorem extcall_captured_unwrap_identity_mem:
  unwrap_value cenv vv sm = (op,su) /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  read_result cx (Value v) es = (INL v,es) /\
  vv_holds cenv cx t (Value v) vv es s /\
  vv_store_bound cx t lt es (Value v) vv s /\
  vv_storage_live cx vv es s /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  evaluate_type (get_tenv cx) lt = SOME ltv /\ val_wf tv v /\
  type_memory_bytes cenv lt = type_memory_size ltv /\
  type_memory_size ltv < dimword (:256) /\
  (!ty src. vv = StackValue ty src ==>
    !x. src = Var x ==> not_fresh_at sm x) /\
  (!ty p. vv = LocatedValue ty p ==>
    (p.ptr_location <> LocMemory \/ is_word_type ty \/ is_word_type lt ==> ty = lt) /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (p.ptr_location <> LocMemory ==> t = lt) /\
    (is_word_type lt /\ p.ptr_location = LocMemory ==>
      !w. eval_operand p.ptr_operand s = SOME w ==>
        w2n w + 32 <= s.vs_alloca_next) /\
    (p.ptr_location = LocCode /\ cenv.ce_is_ctor ==>
      !region. cenv.ce_imm_alloca = SOME region ==>
        eval_operand region s = SOME 0w /\
        (!x. region = Var x ==> not_fresh_at sm x))) /\
  ((?ty src. vv = StackValue ty src) \/
   (?ty p. vv = LocatedValue ty p /\ ~is_word_type ty /\
        ~is_word_type lt /\ p.ptr_location = LocMemory)) ==>
  ?z. gas_path_mem ctx func s 0 (OK z) /\ ~z.vs_halted /\
    z.vs_current_bb = su.cs_current_bb /\
    z.vs_inst_idx = LENGTH su.cs_current_insts /\
    expr_val_rel cx t v op z /\ expr_store_bound cx t v op z /\
    (!w. ~is_word_type t /\ eval_operand op z = SOME w ==>
      type_memory_size ltv = 0 \/
      w2n w + type_memory_size ltv <= z.vs_alloca_next) /\
    (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s) /\
    (!off len. off + len <= s.vs_alloca_next ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH z.vs_memory /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP z.vs_allocas aid = SOME entry) /\
    s.vs_alloca_next <= z.vs_alloca_next /\ alloca_history func z /\
    stmt_state_rel ctx func cenv cx es z /\
    contract_storage z = contract_storage s /\
    contract_transient z = contract_transient s /\
    z.vs_data_section = s.vs_data_section /\ z.vs_labels = s.vs_labels
Proof
  strip_tac >> qpat_x_assum `vv = _` SUBST_ALL_TAC >>
  gvs[unwrap_value_def, comp_return_def] >>
  qexists_tac `s` >>
  simp[gas_path_mem_rules] >>
  gvs[vv_holds_def, expr_store_bound_def, vv_store_bound_def,
    expr_val_rel_def, is_bytestring_type_def, is_word_type_def] >>
  simp[loweringPostsTheory.expr_val_rel_def] >>
  metis_tac[is_word_type_not_bytestring]
QED
