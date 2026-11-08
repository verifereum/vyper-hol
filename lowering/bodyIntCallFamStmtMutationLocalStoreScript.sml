(* Old-variable framing at the same counted local-store endpoint. *)
Theory bodyIntCallFamStmtMutationLocalStore
Ancestors
  bodyIntCallLocalLanding venomState

Theorem protected_local_memory_store_path_frame:
  compile_store_memory cenv src (Var p) ty ty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  expr_val_rel cx ty v src s /\ ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tyv /\ entry.type = tyv /\
  value_has_type tyv v /\ val_wf tyv v /\
  type_memory_bytes cenv ty = type_memory_size tyv /\
  type_memory_size tyv + 64 < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\
  find_containing_scope id es.scopes = SOME (pre,env,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!dw b n. lookup_var p s = SOME dw /\ P b n ==>
    regions_disjoint b n (w2n dw) (type_memory_size tyv)) /\
  (!op x. reserved op /\ op = Var x ==> not_fresh_at sa x) ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    stmt_state_rel ctx func cenv cx
      (es with scopes := pre ++
        (env |+ (id,entry with <|value := v; popped := []|>)) :: rest) u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!b n. P b n ==> mem_bytes_at b n u.vs_memory = mem_bytes_at b n s.vs_memory) /\
    (!op. reserved op ==> eval_operand op u = eval_operand op s) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    (!name b n. local_region cenv
      (pre ++ (env |+ (id,entry with <|value := v; popped := []|>)) :: rest)
      u name b n <=> local_region cenv es.scopes s name b n) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  strip_tac >>
  `!op x. (reserved op \/ ?y. op = Var y /\ not_fresh_at sa y) /\
          op = Var x ==> not_fresh_at sa x` by
    (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  drule_all (BETA_RULE $ Q.INST
    [`reserved` |-> `\op. reserved op \/ ?x. op = Var x /\ not_fresh_at sa x`]
    protected_local_memory_store_path) >>
  strip_tac >> qexists_tac `u` >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!op. _ ==> eval_operand op u = _`
    (qspec_then `Var x` mp_tac) >>
  simp[eval_operand_def]
QED
