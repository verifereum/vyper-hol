(*
 * The loads of a tuple's elements (compile_tuple_load_all) at the
 * elements' types: a word element's value, another element's address.
 *
 * TOP-LEVEL:
 *   compile_tuple_load_all_typed_frag — the loads, as a fragment
 *   tuple_container_bound — a tuple's buffer ends below 2^256
 *)
Theory tupleTypedLoad
Ancestors
  tupleLoadProps tupleMemoryLayout tupleStageProps stmtSimReturn exprSimLeaves
  stmtLowering compileEnv valueEncoding vyperTyping
  list rich_list words arithmetic valueEncodingProofs vyperTypeDefaults
  exprLoweringProps venomMemDefs finite_map exprSim venomState fragExec
  emitHelperProps venomExecSemantics

Theorem tuple_prefix_sizes:
  !tys tvs cenv i.
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs ==>
    SUM (MAP (type_memory_bytes cenv) (TAKE i tys)) =
      SUM (MAP type_memory_size (TAKE i tvs))
Proof
  Induct >> Cases_on `tvs` >> simp[] >>
  rpt gen_tac >> strip_tac >> Cases_on `i` >> simp[] >>
  first_x_assum drule >> simp[]
QED

Theorem tuple_typed_load_value:
  !tys tvs vs tenv cenv (w:256 word) mem i.
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) tys tvs /\
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs /\
    values_have_types tvs vs /\ tuple_in_memory vs tvs (w2n w) mem /\
    w2n w + type_memory_size_list tvs < dimword (:256) /\ i < LENGTH tys ==>
    if is_word_type (EL i tys) then
      mem_word_at (w2n (w + n2w
        (SUM (MAP (type_memory_bytes cenv) (TAKE i tys))))) mem =
          typed_val_to_w256 (EL i tvs) (EL i vs)
    else w2n (w + n2w (SUM (MAP (type_memory_bytes cenv) (TAKE i tys)))) =
      w2n w + SUM (MAP type_memory_size (TAKE i tvs))
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH tys = LENGTH tvs /\ LENGTH tvs = LENGTH vs` by
    metis_tac[LIST_REL_LENGTH, values_have_types_length] >>
  drule tuple_prefix_sizes >> disch_then (qspec_then `i` assume_tac) >>
  `i < LENGTH tvs` by simp[] >>
  drule tuple_element_interval >> strip_tac >>
  `w2n w + SUM (MAP type_memory_size (TAKE i tvs)) < dimword (:256)` by
    gvs[type_memory_size_list_sum] >>
  `w2n (w + n2w (SUM (MAP (type_memory_bytes cenv) (TAKE i tys)))) =
    w2n w + SUM (MAP type_memory_size (TAKE i tvs))` by
    (Cases_on `w` >> gvs[word_add_n2w]) >>
  simp[] >> strip_tac >>
  `LENGTH vs = LENGTH tvs` by simp[] >>
  drule_all tuple_in_memory_element >> strip_tac >>
  qpat_x_assum `LIST_REL (\t tv. evaluate_type tenv t = SOME tv) _ _`
    (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
  disch_then (CONJUNCTS_THEN2 kall_tac (qspec_then `i` mp_tac)) >>
  simp[] >> strip_tac >>
  qpat_x_assum `values_have_types _ _`
    (mp_tac o REWRITE_RULE [values_have_types_LIST_REL, LIST_REL_EL_EQN]) >>
  disch_then (CONJUNCTS_THEN2 kall_tac (qspec_then `i` mp_tac)) >>
  simp[] >> strip_tac >>
  irule val_in_memory_word_type >>
  conj_tac >- (qexistsl_tac [`EL i tys`, `tenv`] >> asm_rewrite_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  once_rewrite_tac[ADD_COMM] >> first_assum ACCEPT_TAC
QED

(* Every live container lies below the allocation frontier. *)
Theorem tuple_container_bound:
  !func cenv cx es s b sz.
    stmt_state_rel func cenv cx es s /\
    ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
     (?name. local_region cenv es.scopes s name b sz)) ==>
    b + sz < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >> fs[stmt_state_rel_def] >> metis_tac[])
  >- (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
      first_x_assum drule >> decide_tac) >>
  fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def, local_region_def] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >> decide_tac
QED

Theorem tuple_load_vars_frame:
  !func cenv cx es sa sb s V.
    stmt_state_rel func cenv cx es s /\ local_ptrs_reserved cenv sa /\
    sa.cs_next_var <= sb.cs_next_var /\
    (!x. not_fresh_at sa x ==>
      lookup_var x (s with vs_vars := V) = lookup_var x s) ==>
    stmt_state_rel func cenv cx es (s with vs_vars := V) /\
    local_ptrs_reserved cenv sb /\
    (!name b sz. local_region cenv es.scopes (s with vs_vars := V) name b sz =
                 local_region cenv es.scopes s name b sz)
Proof
  rpt gen_tac >> strip_tac >>
  `!name entry p sz.
     lookup_scopes name es.scopes = SOME entry /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
     lookup_var p (s with vs_vars := V) = lookup_var p s` by
    (rpt gen_tac >> strip_tac >> first_x_assum irule >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  conj_tac >- (irule stmt_state_rel_vars_frame >> asm_rewrite_tac[]) >>
  conj_tac >- (irule local_ptrs_reserved_next_var >> metis_tac[]) >>
  rpt gen_tac >> rewrite_tac[local_region_def] >>
  eq_tac >> strip_tac >>
  qexistsl_tac [`entry`, `p`, `w`] >> metis_tac[]
QED

Theorem compile_tuple_load_all_typed_run:
  !tys tvs vals tenv cenv bop sa elems sb s w.
    compile_tuple_load_all cenv bop tys 0 sa = (elems,sb) /\
    (!x. bop = Var x ==> not_fresh_at sa x) /\
    eval_operand bop s = SOME w /\
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) tys tvs /\
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs /\
    values_have_types tvs vals /\ tuple_in_memory vals tvs (w2n w) s.vs_memory /\
    w2n w + type_memory_size_list tvs < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    (!x. MEM (Var x) elems ==> not_fresh_at sb x) /\
    LENGTH elems = LENGTH tys /\ EVERY (\op. ?x. op = Var x) elems /\
    ?t V. run_inst_seq (emitted_insts sa sb) s = OK t /\
      t = s with vs_vars := V /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!i. i < LENGTH tys ==> ?v. eval_operand (EL i elems) t = SOME v /\
        if is_word_type (EL i tys) then
          v = typed_val_to_w256 (EL i tvs) (EL i vals)
        else w2n v = w2n w + SUM (MAP type_memory_size (TAKE i tvs)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_tuple_load_all_run >> strip_tac >>
  asm_rewrite_tac[] >> qexistsl_tac [`t`, `vs`] >> asm_rewrite_tac[] >>
  qx_gen_tac `i` >> strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  drule_all tuple_typed_load_value >>
  Cases_on `is_word_type (EL i tys)` >> asm_rewrite_tac[] >>
  strip_tac >> metis_tac[ADD_COMM]
QED

(* Lift a variables-only load run without repeating the compiler induction. *)
Theorem tuple_load_run_lift:
  !ctx func cenv cx es sa sb s t V.
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    t = s with vs_vars := V /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    stmt_state_rel func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
    frag_exec ctx sa sb (\x. x = s)
      (\x. x = t with vs_inst_idx := LENGTH sb.cs_current_insts) (\r. F) /\
    stmt_state_rel func cenv cx es
      (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    local_ptrs_reserved cenv sb /\
    (!name b sz. local_region cenv es.scopes
       (t with vs_inst_idx := LENGTH sb.cs_current_insts) name b sz =
       local_region cenv es.scopes s name b sz)
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (irule frag_exec_run_inst_seq >>
      fs[same_blocks_def, IS_PREFIX_APPEND3] >>
      rpt strip_tac >> metis_tac[]) >>
  `stmt_state_rel func cenv cx es (s with vs_vars := V) /\
   local_ptrs_reserved cenv sb /\
   (!name b sz. local_region cenv es.scopes (s with vs_vars := V) name b sz =
                local_region cenv es.scopes s name b sz)` by
    (irule tuple_load_vars_frame >> conj_tac
     >- (qexists `sa` >> metis_tac[]) >> first_assum ACCEPT_TAC) >>
  conj_tac >- metis_tac[stmt_state_rel_inst_idx] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >>
  `local_region cenv es.scopes (t with vs_inst_idx := LENGTH sb.cs_current_insts)
     name b sz = local_region cenv es.scopes t name b sz` by
    simp[local_region_def, lookup_var_def] >>
  metis_tac[]
QED

Theorem compile_tuple_load_all_typed_frag:
  !tys tvs vals tenv cenv bop sa elems sb s w ctx func cx es.
    compile_tuple_load_all cenv bop tys 0 sa = (elems,sb) /\
    (!x. bop = Var x ==> not_fresh_at sa x) /\
    eval_operand bop s = SOME w /\
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) tys tvs /\
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs /\
    values_have_types tvs vals /\ tuple_in_memory vals tvs (w2n w) s.vs_memory /\
    w2n w + type_memory_size_list tvs < dimword (:256) /\
    stmt_state_rel func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
    LENGTH elems = LENGTH tys /\ EVERY (\op. ?x. op = Var x) elems /\
    (!x. MEM (Var x) elems ==> not_fresh_at sb x) /\
    local_ptrs_reserved cenv sb /\
    ?t. stmt_state_rel func cenv cx es t /\
      frag_exec ctx sa sb (\x. x = s) (\x. x = t) (\r. F) /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      t.vs_halted = s.vs_halted /\ t.vs_memory = s.vs_memory /\
      t.vs_allocas = s.vs_allocas /\
      tuple_in_memory vals tvs (w2n w) t.vs_memory /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!name b sz. local_region cenv es.scopes t name b sz =
                   local_region cenv es.scopes s name b sz) /\
      (!i. i < LENGTH tys ==> ?v. eval_operand (EL i elems) t = SOME v /\
        if is_word_type (EL i tys) then
          v = typed_val_to_w256 (EL i tvs) (EL i vals)
        else w2n v = w2n w + SUM (MAP type_memory_size (TAKE i tvs)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_tuple_load_all_typed_run >> strip_tac >>
  drule_all tuple_load_run_lift >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  asm_rewrite_tac[] >>
  qexists `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  asm_rewrite_tac[] >> simp[] >>
  conj_tac >- (rpt strip_tac >> gvs[lookup_var_def]) >>
  qx_gen_tac `i` >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH tys ==> _`
    (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  qexists `v` >> Cases_on `EL i elems` >>
  gvs[eval_operand_def, lookup_var_def]
QED
