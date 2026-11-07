(* Static readiness and fragment composition for immutable array iteration. *)
Theory whitelistForIterImmFrag
Ancestors
  whitelistForIterImmLoop whitelistForIterDynFrag stmtSimForArrayFrag
  loweringPosts stmtLowering stmtSimProps context emitHelper compileEnv exprLoweringProps
  localPtrsProps emitHelperProps fragExec venomInst list finite_map arithmetic
  allocationPtr stmtSimForArrayLoop stmtSimDeclCompose words fragGasMode
  stmtLoweringMono vyperAST stmtSimDefs gasSummary vyperInterpreter
  vyperState vyperValue gasContext
Libs
  monadsyntax

Theorem immutable_optional_load_ready:
  (if dyn then
     compile_imm_load_word cenv.ce_is_ctor cenv.ce_imm_alloca (Lit (n2w off))
   else return (Lit (n2w cap))) st = (lvo,st1) /\
  local_ptrs_reserved cenv st ==>
  st.cs_next_var <= st1.cs_next_var /\
  local_ptrs_reserved cenv st1 /\
  (!x. not_fresh_at st x ==> not_fresh_at st1 x) /\
  (!x. lvo = Var x ==> not_fresh_at st1 x) /\
  (!l. lvo <> Label l)
Proof
  strip_tac >>
  `st.cs_next_var <= st1.cs_next_var /\
   (!x. lvo = Var x ==> not_fresh_at st1 x) /\ (!l. lvo <> Label l)` by
    (qpat_x_assum `_ st = (lvo,st1)` mp_tac >>
     Cases_on `dyn` >> simp[comp_return_def] >>
     simp[compile_imm_load_word_def] >>
     Cases_on `cenv.ce_is_ctor` >> simp[] >>
     Cases_on `cenv.ce_imm_alloca` >>
     simp[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def, not_fresh_at_def] >>
     rpt strip_tac >> gvs[]) >>
  simp[] >> conj_tac
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `st` >> simp[]) >>
  simp[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]
QED


(* The unused Fixed header dummy is intentionally absent from the distinct
   live-register list: it may coincide with a later copy temporary. *)
Theorem immutable_register_frame:
  local_ptrs_reserved cenv st1 /\
  sa.cs_next_var = st1.cs_next_var + (if dyn then 8 else 5) /\
  sa.cs_next_var <= sj.cs_next_var /\
  p = STRING #"%" (toString st1.cs_next_var) /\
  idx = STRING #"%" (toString (st1.cs_next_var + 1)) /\
  dv = STRING #"%" (toString (st1.cs_next_var + (if dyn then 4 else 2))) /\
  ov = STRING #"%" (toString (st1.cs_next_var + (if dyn then 5 else 3))) /\
  ep = STRING #"%" (toString (st1.cs_next_var + (if dyn then 7 else 4))) /\
  tot = STRING #"%" (toString (st1.cs_next_var + 6)) /\
  nv = STRING #"%" (toString sj.cs_next_var) ==>
  ALL_DISTINCT [p; idx; dv; ov; ep; nv] /\
  p <> tot /\ idx <> tot /\ ov <> tot /\
  (!scs. not_local_ptr cenv scs p /\ not_local_ptr cenv scs idx /\
         not_local_ptr cenv scs dv /\ not_local_ptr cenv scs ov /\
         not_local_ptr cenv scs tot /\ not_local_ptr cenv scs ep /\
         not_local_ptr cenv scs nv) /\
  (!x. not_fresh_at st1 x ==>
    not_fresh_at sa x /\ ~MEM x [p; idx; dv; ov; tot; ep; nv]) /\
  not_fresh_at sa p /\ not_fresh_at sa idx /\ not_fresh_at sa ep
Proof
  strip_tac >>
  `!scs. not_local_ptr cenv scs p /\ not_local_ptr cenv scs idx /\
         not_local_ptr cenv scs dv /\ not_local_ptr cenv scs ov /\
         not_local_ptr cenv scs tot /\ not_local_ptr cenv scs ep /\
         not_local_ptr cenv scs nv` by
    (gen_tac >> rpt conj_tac >> simp[] >>
     irule local_ptrs_reserved_fresh >> qexists_tac `st1` >>
     Cases_on `dyn` >> gvs[]) >>
  Cases_on `dyn` >> gvs[not_fresh_at_def]
QED

Theorem immutable_allocation_ready:
  declare_local cenv id et st1 =
    (bc, st1 with cs_next_var := st1.cs_next_var + 1) /\
  cenv.ce_alloca_locals /\ local_ptrs_reserved cenv st1 /\
  sa.cs_next_var = st1.cs_next_var + (if dyn then 8 else 5) /\
  sa.cs_next_var <= sb0.cs_next_var ==>
  local_ptrs_reserved bc sa /\ local_ptrs_reserved bc sb0 /\
  bc.ce_return_pc = cenv.ce_return_pc /\
  bc.ce_imm_alloca = cenv.ce_imm_alloca /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar
    (Var (STRING #"%" (toString st1.cs_next_var)))
    (type_memory_bytes cenv et)) /\
  (!name. name <> id ==> FLOOKUP bc.ce_vars name = FLOOKUP cenv.ce_vars name)
Proof
  strip_tac >>
  `st1.cs_next_var + 1 <= sa.cs_next_var` by
    (Cases_on `dyn` >> gvs[]) >>
  drule_all array_declared_reserved >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >> gvs[] >>
  qpat_x_assum `_ = cenv` mp_tac >>
  disch_then (fn th =>
    mp_tac (AP_TERM ``\c. c.ce_return_pc`` th) >>
    mp_tac (AP_TERM ``\c. c.ce_imm_alloca`` th)) >> simp[]
QED

(* Transport the two kinds of reserved callers through the generated prefix.
   ret_pc_ok supplies the old return-PC register; local_ptrs_reserved is not
   incorrectly used to reserve that register. *)
Theorem immutable_return_pc_ready:
  bc.ce_return_pc = cenv.ce_return_pc /\ ret_pc_ok cenv st s /\
  st.cs_next_var <= st1.cs_next_var /\
  sa.cs_next_var <= sb0.cs_next_var /\
  (!x. not_fresh_at st1 x ==>
    not_fresh_at sa x /\ ~MEM x [p; idx; dv; ov; tot; ep; nv]) ==>
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) \/
         cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!t. ret_pc_ok cenv st t ==> ret_pc_ok bc sb0 t) /\
  (!x. not_fresh_at st x ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep)
Proof
  strip_tac >>
  `!x. not_fresh_at st x ==> not_fresh_at st1 x` by
    (simp[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb0 x` by
    (simp[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  fs[ret_pc_ok_def, MEM] >> metis_tac[]
QED

(* The counted invariant retains the allocation site, not an explicit address
   bound.  Its state relation recovers that bound at every body entry. *)
Theorem immutable_entry_allocation_bound:
  array_loop_inv ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
    p dst sz ainst bod st k es s /\
  ainst = mk_inst aid ALLOCA [Lit (n2w sz)] [p] /\
  MEM ainst (fn_insts func) /\ sz < dimword (:256) ==>
  w2n dst + sz < dimword (:256)
Proof
  strip_tac >> gvs[array_loop_inv_def, mk_inst_def] >>
  drule_all (SRULE [mk_inst_def] stmt_state_rel_alloca_site_bound) >> simp[]
QED

(* Convert the loop invariant to the copy boundary once, so the fragment
   consumer supplies only the semantic immutable-element observation. *)
Theorem immutable_prepared_entry:
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocCode F et et sa = ((),sb0) /\
  stride = type_memory_size tv /\ 0 < stride /\ stride <= sz /\
  sz < dimword (:256) /\ evaluate_type (get_tenv cx) et = SOME tv /\
  declare_local cenv id et st1 = (bc,sd) /\ cenv.ce_alloca_locals /\
  FLOOKUP cenv.ce_vars id = NONE /\ local_ptrs_reserved bc sa /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  (!scs. not_local_ptr bc (FEMPTY :: scs) p /\
    not_local_ptr cenv scs ov /\ not_local_ptr cenv scs tot /\
    not_local_ptr cenv scs ep) /\
  ALL_DISTINCT [p;idx;ov;ep] /\ p <> tot /\ idx <> tot /\ ov <> tot /\
  not_fresh_at sa ep /\ not_fresh_at sa idx /\
  ainst = mk_inst aid ALLOCA [Lit (n2w sz)] [p] /\
  MEM ainst (fn_insts func) /\ fn_inst_ids_distinct func /\
  sa.cs_current_insts =
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]] ++
    (if dyn then [mk_inst j4 ADD [Lit 32w; Var ov] [tot]] else []) ++
    [mk_inst j5 ADD [Lit (n2w off); Var (if dyn then tot else ov)] [ep]] /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  sb0.cs_current_bb = bod /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) \/
         cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!s. ret_pc_ok cenv st s ==> ret_pc_ok bc sb0 s) /\
  (!x. not_fresh_at caller x ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!ei s k. P ei /\ stmt_state_rel ctx func cenv cx ei s /\ k < LENGTH vs ==>
    immutable_holds cenv cx et (Value (EL k vs))
      (n2w off + n2w ((if dyn then 32 else 0) + k * stride)) ei s) ==>
  !k ei s. array_loop_inv ctx func cenv cx P vs id idx (Lit (n2w off))
      (n2w off) p dst sz ainst bod st k ei s /\ k < LENGTH vs ==>
    ?s2. s2.vs_current_bb = sb0.cs_current_bb /\
      s2.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ~s2.vs_halted /\
      stmt_state_rel ctx func bc cx
        (ei with scopes := (FEMPTY |+ (id,
          <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes) s2 /\
      ret_pc_ok bc sb0 s2 /\ ret_pc_ok cenv st s2 /\
      lookup_var idx s2 = SOME (n2w k) /\ lookup_var p s2 = SOME dst /\
      FLOOKUP s2.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
      array_caller_frame caller s s2 /\ gas_marked_path F ctx func s 0 (OK s2)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `w2n dst + sz < dimword (:256)` by
    (drule_all immutable_entry_allocation_bound >> simp[]) >>
  qpat_x_assum `stride = type_memory_size tv` SUBST_ALL_TAC >>
  fs[array_loop_inv_def] >>
  `cenv_top_ext cenv bc (FEMPTY :: ei.scopes)` by
    (`!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?p sz. l = PtrVar p sz` by simp[] >>
     drule_all cenv_top_ext_declare_local >> simp[]) >>
  `immutable_holds cenv cx et (Value (EL k vs))
    (n2w off + n2w ((if dyn then 32 else 0) + k * type_memory_size tv)) ei s` by
    (qpat_assum `!ei s k. _ ==> immutable_holds _ _ _ _ _ _ _`
       (qspecl_then [`ei`, `s`, `k`] mp_tac) >>
     asm_simp_tac std_ss [ADD_COMM]) >>
  `w2n dst + type_memory_size tv < dimword (:256)` by decide_tac >>
  `ainst.inst_opcode = ALLOCA /\ ainst.inst_outputs = [p]` by simp[mk_inst_def] >>
  `ret_pc_ok bc sb0 s` by metis_tac[] >>
  `not_local_ptr bc (FEMPTY :: ei.scopes) p /\
   not_local_ptr cenv ei.scopes ov /\ not_local_ptr cenv ei.scopes tot /\
   not_local_ptr cenv ei.scopes ep` by metis_tac[] >>
  fs[ALL_DISTINCT] >>
  gvs[] >>
  irule (SRULE [ADD_COMM] immutable_array_entry_run) >>
  asm_simp_tac std_ss [] >>
  qpat_assum `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `sa.cs_current_insts = _` (irule_at Any) >>
  asm_rewrite_tac [] >>
  asm_simp_tac (srw_ss()) [mk_inst_def] >>
  decide_tac
QED
(* A declared pointer is excluded only from scopes in which the new name is absent. *)
Theorem immutable_prepared_entry_guarded:
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocCode F et et sa = ((),sb0) /\
  stride = type_memory_size tv /\ 0 < stride /\ stride <= sz /\
  sz < dimword (:256) /\ evaluate_type (get_tenv cx) et = SOME tv /\
  declare_local cenv id et st1 = (bc,sd) /\ cenv.ce_alloca_locals /\
  FLOOKUP cenv.ce_vars id = NONE /\ local_ptrs_reserved bc sa /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  (!scs. lookup_scopes id scs = NONE ==>
    not_local_ptr bc (FEMPTY :: scs) p /\
    not_local_ptr cenv scs ov /\ not_local_ptr cenv scs tot /\
    not_local_ptr cenv scs ep) /\
  ALL_DISTINCT [p;idx;ov;ep] /\ p <> tot /\ idx <> tot /\ ov <> tot /\
  not_fresh_at sa ep /\ not_fresh_at sa idx /\
  ainst = mk_inst aid ALLOCA [Lit (n2w sz)] [p] /\
  MEM ainst (fn_insts func) /\ fn_inst_ids_distinct func /\
  sa.cs_current_insts =
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]] ++
    (if dyn then [mk_inst j4 ADD [Lit 32w; Var ov] [tot]] else []) ++
    [mk_inst j5 ADD [Lit (n2w off); Var (if dyn then tot else ov)] [ep]] /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  sb0.cs_current_bb = bod /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) \/
         cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!s. ret_pc_ok cenv st s ==> ret_pc_ok bc sb0 s) /\
  (!x. not_fresh_at caller x ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!ei s k. P ei /\ stmt_state_rel ctx func cenv cx ei s /\ k < LENGTH vs ==>
    immutable_holds cenv cx et (Value (EL k vs))
      (n2w off + n2w ((if dyn then 32 else 0) + k * stride)) ei s) ==>
  !k ei s. array_loop_inv ctx func cenv cx P vs id idx (Lit (n2w off))
      (n2w off) p dst sz ainst bod st k ei s /\ k < LENGTH vs ==>
    ?s2. s2.vs_current_bb = sb0.cs_current_bb /\
      s2.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ~s2.vs_halted /\
      stmt_state_rel ctx func bc cx
        (ei with scopes := (FEMPTY |+ (id,
          <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes) s2 /\
      ret_pc_ok bc sb0 s2 /\ ret_pc_ok cenv st s2 /\
      lookup_var idx s2 = SOME (n2w k) /\ lookup_var p s2 = SOME dst /\
      FLOOKUP s2.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
      array_caller_frame caller s s2 /\ gas_marked_path F ctx func s 0 (OK s2)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `w2n dst + sz < dimword (:256)` by
    (drule_all immutable_entry_allocation_bound >> simp[]) >>
  qpat_x_assum `stride = type_memory_size tv` SUBST_ALL_TAC >>
  fs[array_loop_inv_def] >>
  `cenv_top_ext cenv bc (FEMPTY :: ei.scopes)` by
    (`!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?p sz. l = PtrVar p sz` by simp[] >>
     drule_all cenv_top_ext_declare_local >> simp[]) >>
  `immutable_holds cenv cx et (Value (EL k vs))
    (n2w off + n2w ((if dyn then 32 else 0) + k * type_memory_size tv)) ei s` by
    (qpat_assum `!ei s k. _ ==> immutable_holds _ _ _ _ _ _ _`
       (qspecl_then [`ei`, `s`, `k`] mp_tac) >>
     asm_simp_tac std_ss [ADD_COMM]) >>
  `w2n dst + type_memory_size tv < dimword (:256)` by decide_tac >>
  `ainst.inst_opcode = ALLOCA /\ ainst.inst_outputs = [p]` by simp[mk_inst_def] >>
  `ret_pc_ok bc sb0 s` by metis_tac[] >>
  `not_local_ptr bc (FEMPTY :: ei.scopes) p /\
   not_local_ptr cenv ei.scopes ov /\ not_local_ptr cenv ei.scopes tot /\
   not_local_ptr cenv ei.scopes ep` by metis_tac[] >>
  fs[ALL_DISTINCT] >> gvs[] >>
  irule (SRULE [ADD_COMM] immutable_array_entry_run) >>
  asm_simp_tac std_ss [] >>
  qpat_assum `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `sa.cs_current_insts = _` (irule_at Any) >>
  asm_rewrite_tac [] >>
  asm_simp_tac (srw_ss()) [mk_inst_def] >> decide_tac
QED


(* Keep the pre-load return-PC contract while using the post-load compiler
   state to frame the length register introduced by that load. *)
Theorem immutable_initial_frame_rebase:
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz ainst
    cond st1 k es cc /\
  array_caller_frame st1 s0 cc /\ ret_pc_ok cenv st s0 /\
  st.cs_next_var <= st1.cs_next_var ==>
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz ainst
    cond st k es cc
Proof
  strip_tac >>
  `ret_pc_ok cenv st cc` by
    (fs[ret_pc_ok_def, array_caller_frame_def] >> rpt strip_tac >>
     `not_fresh_at st1 x` by
       (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
     metis_tac[]) >>
  fs[array_loop_inv_def] >> asm_rewrite_tac []
QED

(* The length operand is a caller register only after the optional load.
   Preserve that intermediate caller frame for the counted-loop consumer. *)
Theorem immutable_initialize_post_load:
  (if dyn then
     compile_imm_load_word cenv.ce_is_ctor cenv.ce_imm_alloca (Lit (n2w off))
   else return (Lit (n2w cap))) sa = (lvo,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (dyn ==>
    immutable_holds cenv cx (ArrayT et (Dynamic cap)) (Value (ArrayV av))
      (n2w off) es s /\
    evaluate_type (get_tenv cx) et = SOME tv /\
    value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV av) /\
    LENGTH vs = array_length (ArrayTV tv (Dynamic cap)) av) /\
  (~dyn ==> LENGTH vs = cap) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ret_pc_ok cenv sa s /\ sa.cs_next_var <= sb.cs_next_var /\
  ainst.inst_opcode = ALLOCA /\ ainst.inst_outputs = [p] /\
  MEM ainst (fn_insts func) /\ fn_inst_ids_distinct func /\
  ainst.inst_operands = [Lit (n2w sz)] /\ sz < dimword (:256) /\
  lookup_block sb.cs_current_bb func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      sb.cs_current_insts ++ [ainst; mk_inst j JMP [Label entry] []]|> /\
  lookup_block entry func.fn_blocks =
    SOME <|bb_label := entry; bb_instructions :=
      [mk_inst e1 ASSIGN [Lit 0w] [idx]] ++
      (if dyn then
        [mk_inst e2 GT [lvo; Lit (n2w cap)] [g];
         mk_inst e3 ISZERO [Var g] [vld];
         mk_inst e4 ASSERT [Var vld] []] else []) ++
      [mk_inst e5 JMP [Label cond_lbl] []]|> /\
  P es /\ lookup_scopes id es.scopes = NONE /\
  LENGTH vs <= cap /\ cap < dimword (:256) /\
  ALL_DISTINCT [p; idx; g; vld] /\
  not_local_ptr cenv es.scopes p /\ not_local_ptr cenv es.scopes idx /\
  not_local_ptr cenv es.scopes g /\ not_local_ptr cenv es.scopes vld /\
  (!x. lvo = Var x ==> ~MEM x [p; idx; g; vld]) /\
  (!x. not_fresh_at sb x ==> ~MEM x [p; idx; g; vld]) ==>
  ?u dst cc.
    array_loop_inv ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
      p dst sz ainst cond_lbl sa 0 es cc /\
    eval_operand lvo u = SOME (n2w (LENGTH vs)) /\
    eval_operand lvo cc = SOME (n2w (LENGTH vs)) /\
    array_caller_frame sa s u /\ array_caller_frame sb u cc /\
    gas_marked_path F ctx func s 0 (OK cc)
Proof
  strip_tac >> drule_all immutable_optional_length_boundary >> strip_tac >>
  `ret_pc_ok cenv sb u` by
    (fs[ret_pc_ok_def, not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `lookup_block u.vs_current_bb func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      sb.cs_current_insts ++ [ainst; mk_inst j JMP [Label entry] []]|>` by simp[] >>
  drule_all immutable_allocate_initialize >>
  disch_then (qspec_then `off` strip_assume_tac) >>
  `array_loop_inv ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
      p dst sz ainst cond_lbl sa 0 es cc` by
    (irule immutable_initial_frame_rebase >> goal_assum (drule_at Any) >>
     asm_rewrite_tac []) >>
  qexistsl_tac [`u`, `dst`, `cc`] >> asm_rewrite_tac [] >>
  drule_all gas_marked_path_then >> simp[]
QED

(* Isolate gas normalization and the declared-local environment extension from
   the semantic body and restoration callbacks used by the public fragment. *)
Theorem immutable_body_callbacks:
  declare_local cenv id et st1 = (bc,sd) /\ cenv.ce_alloca_locals /\
  FLOOKUP cenv.ce_vars id = NONE /\
  (!ei k. P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs ==>
    stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
      (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
      (ei with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes)) /\
  (!ei k gs r es2. P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs /\
    eval_stmts cx stmts (ei with <|scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes;
      gas_obs := gs|>) = (r,es2) ==>
    (!ex inc. stmt_res_ok (InLoop ex inc) r) /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)) ==>
  !ei k. P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs ==>
    cenv_top_ext cenv bc ((FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes) /\
    stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
      (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
      (ei with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes;
        gas_obs := []|>) /\
    (!gs r es2. eval_stmts cx stmts
      (ei with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes;
        gas_obs := gs|>) = (r,es2) ==>
      stmt_res_ok (InLoop exit_lbl incr_lbl) r /\
      ?sc rest. es2.scopes = sc :: rest /\
        (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
        ((r = INL () \/ r = INR ContinueException) ==>
          P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> conj_tac
  >- (irule cenv_top_ext_declare_local >>
      qpat_assum `declare_local _ _ _ _ = _` (irule_at Any) >> simp[]) >>
  conj_tac
  >- (qpat_assum `!ei k. _` drule_all >> strip_tac >>
      drule stmt_frag_start_gas_obs >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!ei k gs r es2. _` drule_all >> strip_tac >>
  conj_tac >- metis_tac[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem immutable_compiled_loop_outcome:
  !ctx func cx cenv lctx RetQ ty id et bd n src name off stmts tv vs es P st st' s.
  FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  cenv.ce_alloca_locals /\ FLOOKUP cenv.ce_vars id = NONE /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  elem_size_in_location cenv LocCode et = type_memory_size tv /\
  type_memory_bytes cenv et = type_memory_size tv /\
  0 < type_memory_size tv /\ type_memory_bytes cenv et + 64 < dimword (:256) /\
  LENGTH vs <= bound_length bd /\ bound_length bd < dimword (:256) /\
  (case bd of Fixed cap => LENGTH vs = cap | Dynamic cap => T) /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==> cs_extends sa sb) /\
  (!ei s. P ei /\ stmt_state_rel ctx func cenv cx ei s ==>
    (case bd of Fixed cap => T | Dynamic cap =>
       ?av. immutable_holds cenv cx (ArrayT et (Dynamic cap))
               (Value (ArrayV av)) (n2w off) ei s /\
            value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV av) /\
            LENGTH vs = array_length (ArrayTV tv (Dynamic cap)) av) /\
    (!k. k < LENGTH vs ==> immutable_holds cenv cx et (Value (EL k vs))
      (n2w off + n2w ((case bd of Fixed cap => 0 | Dynamic cap => 32) +
                      k * type_memory_size tv)) ei s)) /\
  (!st0 bc sd ex inc ei k.
    declare_local cenv id et st0 = (bc,sd) /\ P ei /\
    lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs ==>
    stmt_frag ctx func cx (InLoop ex inc) RetQ bc
      (stmts_env bc (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
      (ei with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes)) /\
  (!ei k gs r es2. P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs /\
    eval_stmts cx stmts (ei with <|scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes;
      gas_obs := gs|>) = (r,es2) ==>
    (!ex inc. stmt_res_ok (InLoop ex inc) r) /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)) /\
  compile_stmt cenv lctx ty
    (For id et (Array (TopLevelName (ArrayT et bd) (src,name))) n stmts) st = ((),st') /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv st /\ ret_pc_ok cenv st s /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  P es /\ lookup_scopes id es.scopes = NONE /\
  gas_admissible (eval_for cx tv id stmts vs) (stmt_res_ok lctx) es ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_for cx tv id stmts vs) (es,s)
    (\res ee t. res = INL () /\
       t.vs_current_bb = st'.cs_current_bb /\
       t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
       stmt_state_rel ctx func cenv cx ee t /\ array_caller_frame st s t)
    (\res ee r. ?ex. res = INR ex /\
       !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) r)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_for_immutable_entry_code_normalized >> strip_tac >>
  drule_all immutable_optional_load_ready >> strip_tac >>
  `sb0.cs_next_var <= sb1.cs_next_var` by
    (mp_tac (cj 2 compile_stmt_cs_mono) >>
     simp[cs_mono_def] >> disch_then drule >> simp[]) >>
  `sa.cs_next_var <= sj.cs_next_var` by decide_tac >>
  `sa.cs_next_var <= sb0.cs_next_var` by
    (mp_tac (cj 6 ci_mono_stmt_helpers) >>
     qpat_assum `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[ci_mono_def] >> metis_tac[pairTheory.SND]) >>
  qabbrev_tac `tot = STRING #"%" (toString (st1.cs_next_var + 6))` >>
  `tot = STRING #"%" (toString (st1.cs_next_var + 6))` by simp[Abbr `tot`] >>
  drule_all immutable_register_frame >> strip_tac >>
  drule_all immutable_allocation_ready >> strip_tac >>
  drule_all immutable_return_pc_ready >> strip_tac >>
  `fn_has_code st st1 func` by
    (irule (cj 1 fn_has_code_split) >> asm_rewrite_tac [] >>
     qexists_tac `st'` >> asm_rewrite_tac [] >> metis_tac[cs_extends_trans]) >>
  qabbrev_tac `ainst = mk_inst st1.cs_next_id ALLOCA
    [Lit (n2w (type_memory_bytes cenv et))] [p]` >>
  `MEM ainst (fn_insts func)` by
    (irule lookup_block_fn_insts >>
     qpat_assum `lookup_block st1.cs_current_bb _ = _` (irule_at Any) >>
     simp[Abbr `ainst`]) >>
  qabbrev_tac `g = STRING #"%" (toString (st1.cs_next_var + 2))` >>
  qabbrev_tac `vld = STRING #"%" (toString (st1.cs_next_var + 3))` >>
  `ALL_DISTINCT [p;idx;g;vld] /\
   (!scopes. not_local_ptr cenv scopes g /\ not_local_ptr cenv scopes vld) /\
   (!x. not_fresh_at st1 x ==> ~MEM x [p;idx;g;vld])` by
    (simp[Abbr `g`, Abbr `vld`, not_fresh_at_def] >>
     rpt conj_tac >> rpt gen_tac >> rpt strip_tac >>
     irule local_ptrs_reserved_fresh >> qexists_tac `st1` >> simp[]) >>
  `!x. lvo = Var x ==> ~MEM x [p;idx;g;vld]` by metis_tac[] >>
  `?u dst cc.
    array_loop_inv ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
      p dst (type_memory_bytes cenv et) ainst cond st 0 es cc /\
    eval_operand lvo u = SOME (n2w (LENGTH vs)) /\
    eval_operand lvo cc = SOME (n2w (LENGTH vs)) /\
    array_caller_frame st s u /\ array_caller_frame st1 u cc /\
    gas_marked_path F ctx func s 0 (OK cc)` by
    (qpat_assum `!ei s. P ei /\ stmt_state_rel _ _ _ _ _ _ ==> _` drule_all >>
     strip_tac >>
     irule immutable_initialize_post_load >>
     qpat_assum `(if dyn then _ else _) st = (lvo,st1)` (irule_at Any) >>
     qpat_assum `lookup_block entry _ = _` (irule_at Any) >>
     asm_rewrite_tac [] >>
     simp[Abbr `ainst`, mk_inst_def, Abbr `g`, Abbr `vld`] >>
     qexistsl_tac [`tv`, `et`] >>
     qpat_x_assum `case bd of Fixed cap => LENGTH vs = cap | Dynamic cap => T` mp_tac >>
     qpat_x_assum `case bd of Fixed cap => T | Dynamic cap => _` mp_tac >>
     qpat_x_assum `evaluate_type _ et = SOME tv` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `bd` >> simp[bound_length_def] >> metis_tac[]) >>
  `?bb. lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
      isPREFIX sb0.cs_current_insts bb.bb_instructions` by
    (irule fn_has_code_start >> qexists_tac `sb1` >> asm_rewrite_tac []) >>
  `!t. ret_pc_ok cenv st t ==> ret_pc_ok bc sb0 t` by
    (rpt strip_tac >> irule ret_pc_ok_frame >>
     qexistsl_tac [`cenv`, `t`, `st`] >>
     asm_rewrite_tac [] >> conj_tac >- metis_tac[] >>
     `st1.cs_next_var <= sa.cs_next_var` by
       (qpat_assum `sa.cs_next_var = _` mp_tac >> simp[]) >> decide_tac) >>
  `!x. not_fresh_at st1 x ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep` by
    (qpat_x_assum `!x. not_fresh_at st1 x ==> not_fresh_at sa x /\ ~MEM x _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[MEM] >> metis_tac[]) >>
  `!scs. lookup_scopes id scs = NONE ==>
    not_local_ptr bc (FEMPTY :: scs) p /\
    not_local_ptr cenv scs ov /\ not_local_ptr cenv scs tot /\
    not_local_ptr cenv scs ep` by
    (gen_tac >> disch_tac >> conj_tac
     >- (irule not_local_ptr_name_update >> qexists_tac `cenv` >>
         asm_rewrite_tac [] >> metis_tac[]) >> metis_tac[]) >>
  `!ei t k. P ei /\ stmt_state_rel ctx func cenv cx ei t /\ k < LENGTH vs ==>
    immutable_holds cenv cx et (Value (EL k vs))
      (n2w off + n2w ((if dyn then 32 else 0) + k * type_memory_size tv)) ei t` by
    (qpat_x_assum `!ei s. P ei /\ stmt_state_rel _ _ _ _ _ _ ==> _` mp_tac >>
     qpat_x_assum `dyn <=> _` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `bd` >> simp[] >> metis_tac[]) >>
  `ALL_DISTINCT [p;idx;ov;ep]` by
    (qpat_x_assum `ALL_DISTINCT [p;idx;dv;ov;ep;nv]` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[ALL_DISTINCT] >> metis_tac[]) >>
  `local_ptrs_reserved bc sb0` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> asm_rewrite_tac []) >>
  `!k ei t. array_loop_inv ctx func cenv cx P vs id idx (Lit (n2w off))
      (n2w off) p dst (type_memory_bytes cenv et) ainst bod st k ei t /\ k < LENGTH vs ==>
    ?s2. s2.vs_current_bb = sb0.cs_current_bb /\
      s2.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ~s2.vs_halted /\
      stmt_state_rel ctx func bc cx
        (ei with scopes := (FEMPTY |+ (id,
          <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes) s2 /\
      ret_pc_ok bc sb0 s2 /\ ret_pc_ok cenv st s2 /\
      lookup_var idx s2 = SOME (n2w k) /\ lookup_var p s2 = SOME dst /\
      FLOOKUP s2.vs_allocas ainst.inst_id = SOME (w2n dst,type_memory_bytes cenv et) /\
      array_caller_frame st1 t s2 /\ gas_marked_path F ctx func t 0 (OK s2)` by
    (rpt gen_tac >> strip_tac >>
     irule (Q.INST [`tot` |-> `tot`, `ov` |-> `ov`, `dyn` |-> `dyn`]
       (SPEC_ALL immutable_prepared_entry_guarded)) >>
     qpat_assum `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `declare_local _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `array_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `elem_size_in_location cenv LocCode et = _`
       (fn th => pure_rewrite_tac [th]) >>
     qpat_assum `lookup_block sb0.cs_current_bb _ = _` (irule_at Any) >>
     qexistsl_tac [`tot`, `ov`] >>
     qexistsl_tac [`h + (if dyn then 2 else 1)`, `h+1`, `h`] >>
     qexistsl_tac [`dyn`, `st1.cs_next_id`] >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       (qpat_assum `!scs. lookup_scopes id scs = NONE ==> _` ACCEPT_TAC),
       (qpat_assum `!ei t k. _ ==> immutable_holds _ _ _ _ _ _ _` ACCEPT_TAC),
       (qpat_assum `type_memory_bytes cenv et + 64 < _` mp_tac >>
        rpt (pop_assum kall_tac) >> decide_tac),
       (qpat_assum `type_memory_bytes cenv et = _`
          (fn th => simp_tac std_ss [th]) >> NO_TAC),
       (simp_tac std_ss [Abbr `ainst`, mk_inst_def] >> NO_TAC),
       (qpat_assum `sa.cs_current_insts = _` (fn a =>
        qpat_assum `elem_size_in_location cenv LocCode et = _`
          (fn b => pure_rewrite_tac [a,b])) >>
        qpat_x_assum `toto = _` mp_tac >>
        qpat_x_assum `ov = _` mp_tac >>
        qpat_x_assum `tot = _` mp_tac >>
        rpt (pop_assum kall_tac) >> Cases_on `dyn` >> simp[] >> NO_TAC),
       (FAIL_TAC "entry residual")]) >>
  `!ei k. P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs ==>
    cenv_top_ext cenv bc ((FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes) /\
    stmt_frag ctx func cx (InLoop exit incr) RetQ bc
      (stmts_env bc (InLoop exit incr) ty stmts) (eval_stmts cx stmts)
      (ei with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes;
        gas_obs := []|>) /\
    (!gs r es2. eval_stmts cx stmts
      (ei with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes;
        gas_obs := gs|>) = (r,es2) ==>
      stmt_res_ok (InLoop exit incr) r /\
      ?sc rest. es2.scopes = sc :: rest /\
        (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
        ((r = INL () \/ r = INR ContinueException) ==>
          P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE))` by
    (match_mp_tac (Q.INST [`et` |-> `et`, `st1` |-> `st1`,
       `sd` |-> `st1 with cs_next_var := st1.cs_next_var + 1`]
       (SPEC_ALL immutable_body_callbacks)) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       (rpt gen_tac >> strip_tac >>
        qpat_assum `!st0 bc sd ex inc ei k. _` drule_all >> simp[])]) >>
  `?bc'. stmts_env bc (InLoop exit incr) ty stmts sb0 = (bc',sb1)` by
    (qpat_assum `compile_stmts bc _ _ _ sb0 = _` mp_tac >>
     once_rewrite_tac [compile_stmts_env] >>
     Cases_on `stmts_env bc (InLoop exit incr) ty stmts sb0` >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb0 x` by
    (qpat_assum `sa.cs_next_var <= sb0.cs_next_var` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `!x. not_fresh_at st1 x ==>
     not_fresh_at sb0 x /\ x <> idx /\ x <> nv /\ x <> dv` by
    (qpat_x_assum `!x. not_fresh_at st1 x ==> not_fresh_at sa x /\ ~MEM x _` mp_tac >>
     qpat_x_assum `!x. not_fresh_at sa x ==> not_fresh_at sb0 x` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[MEM] >> metis_tac[]) >>
  `!scs. not_local_ptr cenv scs idx /\ not_local_ptr cenv scs nv /\
      not_local_ptr cenv scs dv` by
    (qpat_x_assum `!scs. not_local_ptr cenv scs p /\ _` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  `dv <> idx /\ dv <> p /\ p <> idx /\ p <> nv` by
    (qpat_x_assum `ALL_DISTINCT [p;idx;dv;ov;ep;nv]` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[ALL_DISTINCT] >> metis_tac[]) >>
  `not_fresh_at sb0 idx /\ not_fresh_at sb0 p` by metis_tac[] >>
  `(~block_is_terminated sb1 ==> sj.cs_blocks = sb1.cs_blocks /\
     sj.cs_current_bb = sb1.cs_current_bb /\
     sj.cs_current_insts = sb1.cs_current_insts ++
       [mk_inst sb1.cs_next_id JMP [Label incr] []] /\ fn_has_code sb1 sj func)` by
    (qpat_x_assum `~block_is_terminated sb1 ==> _` mp_tac >>
     qpat_x_assum `fn_has_code sb1 sj func` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `gas_outcome F (cx_tops cx) (ctx,func)
    (eval_for cx tv id stmts vs) (es,cc)
    (\res ee t. res = INL () /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\
      ~t.vs_halted /\ stmt_state_rel ctx func cenv cx ee t /\
      array_caller_frame st1 u t)
    (\res ee r. ?ex. res = INR ex /\
      !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) r)` by
    (irule (SRULE [] (Q.INST [`k` |-> `0`] (SPEC_ALL immutable_for_loop_counted))) >>
     qpat_assum `array_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 _ _` (irule_at Any) >>
     qpat_assum `stmts_env bc _ _ _ sb0 = _` (irule_at Any) >>
     qpat_assum `lookup_block cond _ = _` (irule_at Any) >>
     qpat_assum `lookup_block incr _ = _` (irule_at Any) >>
     qexistsl_tac [`sj`, `lctx`] >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       (qpat_assum `LENGTH vs <= bound_length bd` mp_tac >>
        qpat_assum `bound_length bd < _` mp_tac >>
        rpt (pop_assum kall_tac) >> decide_tac),
       (FAIL_TAC "loop residual")]) >>
  irule gas_outcome_zero_prefix >>
  qpat_assum `gas_marked_path F ctx func s 0 (OK cc)` (irule_at Any) >>
  irule exprSimMemDefsTheory.gas_outcome_post_mono >>
  qpat_assum `gas_outcome _ _ _ _ (es,cc) _ _` (irule_at Any) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  qpat_assum `st'.cs_current_bb = exit` (fn th => pure_rewrite_tac [th]) >>
  qpat_assum `st'.cs_current_insts = []` (fn th => pure_rewrite_tac [th]) >>
  simp_tac std_ss [listTheory.LENGTH] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    (qpat_assum `array_caller_frame st s u` mp_tac >>
     qpat_assum `array_caller_frame st1 u t` mp_tac >>
     qpat_assum `!x. not_fresh_at st x ==> not_fresh_at st1 x` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[array_caller_frame_def] >> metis_tac[])]
QED

Theorem compile_for_immutable_final_insts[local]:
  FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  compile_stmt cenv lctx ty
    (For id et (Array (TopLevelName (ArrayT et bd) (src,name))) n stmts) st = ((),st') /\
  cenv.ce_alloca_locals /\ fn_has_code st st' func /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==> cs_extends sa sb) ==>
  st'.cs_current_insts = []
Proof
  strip_tac >> drule_all compile_for_immutable_entry_code_normalized >>
  strip_tac >> asm_rewrite_tac[]
QED

Theorem compile_for_immutable_frag_zero:
  !ctx func cx cenv lctx RetQ ty id et bd n src name off stmts tv vs es P.
  FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  cenv.ce_alloca_locals /\ FLOOKUP cenv.ce_vars id = NONE /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  elem_size_in_location cenv LocCode et = type_memory_size tv /\
  type_memory_bytes cenv et = type_memory_size tv /\
  0 < type_memory_size tv /\ type_memory_bytes cenv et + 64 < dimword (:256) /\
  LENGTH vs <= bound_length bd /\ bound_length bd < dimword (:256) /\
  (case bd of Fixed cap => LENGTH vs = cap | Dynamic cap => T) /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==> cs_extends sa sb) /\
  (!ei s. P ei /\ stmt_state_rel ctx func cenv cx ei s ==>
    (case bd of Fixed cap => T | Dynamic cap =>
       ?av. immutable_holds cenv cx (ArrayT et (Dynamic cap))
               (Value (ArrayV av)) (n2w off) ei s /\
            value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV av) /\
            LENGTH vs = array_length (ArrayTV tv (Dynamic cap)) av) /\
    (!k. k < LENGTH vs ==> immutable_holds cenv cx et (Value (EL k vs))
      (n2w off + n2w ((case bd of Fixed cap => 0 | Dynamic cap => 32) +
                      k * type_memory_size tv)) ei s)) /\
  (!st0 bc sd ex inc ei k.
    declare_local cenv id et st0 = (bc,sd) /\ P ei /\
    lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs ==>
    stmt_frag ctx func cx (InLoop ex inc) RetQ bc
      (stmts_env bc (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
      (ei with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes)) /\
  (!ei k gs r es2. P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs /\
    eval_stmts cx stmts (ei with <|scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes;
      gas_obs := gs|>) = (r,es2) ==>
    (!ex inc. stmt_res_ok (InLoop ex inc) r) /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)) /\
  bound_length bd <= n /\ lookup_scopes id es.scopes = NONE /\
  P (es with gas_obs := []) /\
  (!gs. eval_iterator cx (Array (TopLevelName (ArrayT et bd) (src,name)))
    (es with gas_obs := gs) = (INL vs, es with gas_obs := gs)) ==>
  stmt_frag ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty
      (For id et (Array (TopLevelName (ArrayT et bd) (src,name))) n stmts))
    (eval_stmt cx
      (For id et (Array (TopLevelName (ArrayT et bd) (src,name))) n stmts)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >>
  map_every qx_gen_tac [`st`, `st'`, `s0`, `cenv'`] >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
     simp[stmt_state_rel_def, state_rel_gas_obs, immutable_alloca_sep_def, NoAsms] >>
     strip_tac >> asm_rewrite_tac[]) >>
  `lookup_scopes id (es with gas_obs := []).scopes = NONE` by simp[] >>
  `LENGTH vs <= n` by decide_tac >>
  `gas_admissible (eval_for cx tv id stmts vs) (stmt_res_ok lctx)
     (es with gas_obs := [])` by
    (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[gas_admissible_def, Once evaluate_def, lift_option_type_def,
       lift_option_def, bind_return, bind_def, compatible_bound_def,
       check_def, vyperStateTheory.assert_def, ignore_bind_def, return_def]) >>
  mp_tac (Q.INST [`es` |-> `es with gas_obs := []`, `st'` |-> `cs'`,
                  `s` |-> `s0`] (SPEC_ALL immutable_compiled_loop_outcome)) >>
  impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  drule_all for_source_prefix_bounded >> strip_tac >>
  drule_all compile_for_immutable_final_insts >> strip_tac >>
  gvs[] >> irule array_outcome_stmt_post >> simp[] >> first_assum ACCEPT_TAC
QED
