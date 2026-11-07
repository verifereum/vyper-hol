(* Static readiness and fragment composition for immutable array iteration. *)
Theory whitelistForIterImmFrag
Ancestors
  whitelistForIterImmLoop whitelistForIterDynFrag stmtSimForArrayFrag
  loweringPosts stmtLowering stmtSimProps context emitHelper compileEnv exprLoweringProps
  localPtrsProps emitHelperProps fragExec venomInst list finite_map arithmetic
  allocationPtr stmtSimForArrayLoop stmtSimDeclCompose words fragGasMode
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
