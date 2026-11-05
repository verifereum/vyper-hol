(* Proof interfaces for the fixed-array loop; no executable compiler here. *)
Theory stmtSimForArrayLoop
Ancestors
  loweringPosts stmtSimDefs stmtSimProps
  stmtSimForArrayParts stmtSimForArray  stmtLowering compileEnv
  fragExec loweringSlice localPtrsProps exprLoweringProps emitHelper
  venomInst venomState venomExecSemantics vyperState valueEncoding
  list rich_list finite_map words integer_word venomExecProofs emitHelperProps
  vyperEvalPreservesScopes stmtSimForParts vyperInterpreter

Definition array_for_code_def:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj <=>
    lookup_block cond_lbl func.fn_blocks =
      SOME <| bb_label := cond_lbl;
              bb_instructions :=
                [mk_inst j1 EQ [Var idx; Lit (n2w n)] [dv];
                 mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []] |> /\
    lookup_block incr_lbl func.fn_blocks =
      SOME <| bb_label := incr_lbl;
              bb_instructions :=
                [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
                 mk_inst i2 ASSIGN [Var nv] [idx];
                 mk_inst i3 JMP [Label cond_lbl] []] |> /\
    sa.cs_current_bb = stmts_lbl /\
    sa.cs_current_insts =
      [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
       mk_inst j4 ADD [saved_base; Var ov] [ep]] /\
    compile_iter_elem_copy cenv (Var ep) (Var p) stride LocMemory F et et sa =
      ((),sb0) /\
    sb0.cs_current_bb = stmts_lbl /\
    sb0.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb0 /\
    same_blocks sa sb0 /\ fn_has_code sa sb0 func /\
    compile_stmts bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = ((),sb1) /\
    fn_has_code sb0 sb1 func /\ local_ptrs_reserved bc sa /\
    local_ptrs_reserved bc sb0 /\
    ~block_is_terminated sb0 /\
    (~block_is_terminated sb1 ==>
       sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
       sj.cs_current_insts = sb1.cs_current_insts ++
         [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\
       fn_has_code sb1 sj func) /\
    fn_inst_ids_distinct func /\
    MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
    ainst.inst_outputs = [p] /\
    FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
    (!name. name <> id ==> FLOOKUP bc.ce_vars name = FLOOKUP cenv.ce_vars name) /\
    bc with <| ce_vars := cenv.ce_vars; ce_var_type := cenv.ce_var_type;
               ce_dynarray_capacity := cenv.ce_dynarray_capacity |> = cenv /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    (!scs. not_local_ptr cenv scs idx /\ not_local_ptr cenv scs dv /\
           not_local_ptr cenv scs ov /\ not_local_ptr cenv scs ep /\
           not_local_ptr cenv scs nv) /\
    ALL_DISTINCT [idx; dv; ov; ep; nv; p] /\
    (!x. saved_base = Var x ==> ~MEM x [idx; dv; ov; ep; nv]) /\
    not_fresh_at sa idx /\ not_fresh_at sa p /\ not_fresh_at sa ep /\
    (!x. saved_base = Var x ==> not_fresh_at sa x) /\
    stride = type_memory_bytes cenv et /\ stride = type_memory_size tv /\
    stride <= sz /\ stride + 64 < dimword (:256)
End

Definition array_loop_inv_def:
  array_loop_inv ctx func cenv cx P vs id idx saved_base base p dst sz
    ainst cond_lbl st k es s <=>
    s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    stmt_state_rel ctx func cenv cx es s /\ P es /\
    lookup_scopes id es.scopes = NONE /\ k <= LENGTH vs /\
    lookup_var idx s = SOME (n2w k) /\
    eval_operand saved_base s = SOME base /\
    lookup_var p s = SOME dst /\
    FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
    ret_pc_ok cenv st s
End

Theorem array_copy_prefix_alignment:
  sa.cs_current_insts =
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [saved_base; Var ov] [ep]] /\
  sb0.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb0 ==>
  sb0.cs_current_insts =
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [saved_base; Var ov] [ep]] ++ emitted_insts sa sb0 /\
  LENGTH sb0.cs_current_insts = 2 + LENGTH (emitted_insts sa sb0)
Proof
  simp[]
QED

Theorem array_for_code_condition:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj ==>
  lookup_block cond_lbl func.fn_blocks =
    SOME <| bb_label := cond_lbl;
            bb_instructions :=
              [mk_inst j1 EQ [Var idx; Lit (n2w n)] [dv];
               mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []] |>
Proof
  simp[array_for_code_def]
QED

Theorem array_for_code_increment:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj ==>
  lookup_block incr_lbl func.fn_blocks =
    SOME <| bb_label := incr_lbl;
            bb_instructions :=
              [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
               mk_inst i2 ASSIGN [Var nv] [idx];
               mk_inst i3 JMP [Label cond_lbl] []] |>
Proof
  simp[array_for_code_def]
QED

Theorem array_for_code_prefix:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj ==>
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocMemory F et et sa =
    ((),sb0) /\
  sb0.cs_current_insts =
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [saved_base; Var ov] [ep]] ++ emitted_insts sa sb0 /\
  LENGTH sb0.cs_current_insts = 2 + LENGTH (emitted_insts sa sb0) /\
  sb0.cs_current_bb = stmts_lbl
Proof
  strip_tac >> fs[array_for_code_def]
QED

Theorem array_for_code_stmts:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj ==>
  compile_stmts bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = ((),sb1) /\
  fn_has_code sb0 sb1 func /\ local_ptrs_reserved bc sb0 /\
  ~block_is_terminated sb0
Proof
  simp[array_for_code_def]
QED

Theorem array_for_code_scope_frame:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  lookup_scopes id scopes = NONE ==>
  cenv_top_ext cenv bc (FEMPTY :: scopes)
Proof
  simp[array_for_code_def, cenv_top_ext_def] >> rpt strip_tac >>
  rename1 `FLOOKUP bc.ce_vars name <> FLOOKUP cenv.ce_vars name` >>
  `name = id` by
    (spose_not_then assume_tac >>
     qpat_x_assum `!name. name <> id ==> _`
       (qspec_then `name` mp_tac) >> simp[]) >>
  gvs[lookup_scopes_def] >> metis_tac[]
QED

(* The prefix length is derived from the actual two emit_op calls and the
   copy append interface, rather than fixed to the range loop's MSTORE. *)
Theorem array_emitted_prefix_alignment:
  s0.cs_current_insts = [] /\
  emit_op MUL [Var idx; Lit (n2w stride)] s0 = (Var ov,s1) /\
  emit_op ADD [saved_base; Var ov] s1 = (Var ep,sa) /\
  sb0.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb0 ==>
  sb0.cs_current_insts =
    [mk_inst s0.cs_next_id MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst s1.cs_next_id ADD [saved_base; Var ov] [ep]] ++
      emitted_insts sa sb0 /\
  LENGTH sb0.cs_current_insts = 2 + LENGTH (emitted_insts sa sb0)
Proof
  rpt strip_tac >>
  imp_res_tac emitHelperPropsTheory.emitted_insts_emit_op >> gvs[]
QED

Theorem array_condition_block:
  !ctx func cc idx dv a b lbl exit_lbl stmts_lbl j1 j2.
    lookup_block lbl func.fn_blocks =
      SOME <| bb_label := lbl;
              bb_instructions :=
                [mk_inst j1 EQ [Var idx; Lit b] [dv];
                 mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []] |> /\
    cc.vs_current_bb = lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    lookup_var idx cc = SOME a ==>
    !fuel rr.
      run_from fuel ctx func
        (jump_to (if a = b then exit_lbl else stmts_lbl)
           (update_var dv (bool_to_word (a = b)) cc)) = rr /\
      (!e. rr <> Error e) ==>
      ?fuel'. run_from fuel' ctx func cc = rr
Proof
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `lookup_block lbl _ = SOME bb` >>
  `!fu. run_from fu ctx func cc =
        run_from fu ctx func
          (update_var dv (bool_to_word (a = b)) cc with vs_inst_idx := 1)` by
    (gen_tac >>
     `run_from fu ctx func cc = run_from fu ctx func
        (update_var dv (bool_to_word (a = b)) cc with
           vs_inst_idx := SUC cc.vs_inst_idx)` suffices_by simp[] >>
     irule run_from_step >>
     qexistsl_tac [`bb`, `mk_inst j1 EQ [Var idx; Lit b] [dv]`] >>
     simp[Abbr `bb`, get_instruction_def, mk_inst_def, is_terminator_def] >>
     simp[GSYM mk_inst_def] >> irule step_EQ >> simp[eval_operand_def]) >>
  qabbrev_tac `d1 = update_var dv (bool_to_word (a = b)) cc with vs_inst_idx := 1` >>
  `jump_to (if a = b then exit_lbl else stmts_lbl) d1 =
   jump_to (if a = b then exit_lbl else stmts_lbl)
     (update_var dv (bool_to_word (a = b)) cc)` by
    simp[Abbr `d1`, jump_to_def, update_var_def] >>
  rpt strip_tac >> qexists_tac `SUC fuel` >>
  `run_from (SUC fuel) ctx func d1 = rr` by
    (irule run_from_jump_result >>
     simp[Abbr `d1`, update_var_def] >>
     qexistsl_tac [
       `mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []`,
       `if a = b then exit_lbl else stmts_lbl`] >>
     simp[Abbr `bb`, get_instruction_def,
          mk_inst_def, is_terminator_def, update_var_def] >>
     Cases_on `a = b` >>
     gvs[step_inst_base_def, bool_to_word_def, eval_operand_def,
          lookup_var_def, FLOOKUP_UPDATE, jump_to_def, update_var_def]) >>
  fs[]
QED

Theorem array_condition_boundary:
  !ctx func cenv cx P vs id idx saved_base base p dst sz ainst cond_lbl st
   k es cc n dv j1 j2 exit_lbl stmts_lbl.
  lookup_block cond_lbl func.fn_blocks =
    SOME <| bb_label := cond_lbl;
            bb_instructions :=
              [mk_inst j1 EQ [Var idx; Lit (n2w n)] [dv];
               mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []] |> /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base base p dst sz
    ainst cond_lbl st k es cc /\
  n = LENGTH vs /\ n < dimword (:256) /\
  not_local_ptr cenv es.scopes dv /\ dv <> idx /\ dv <> p /\
  (!x. saved_base = Var x ==> x <> dv) ==>
  ?next.
    array_loop_inv ctx func cenv cx P vs id idx saved_base base p dst sz
      ainst (if k = n then exit_lbl else stmts_lbl) st k es next /\
    (!x. x <> dv ==> lookup_var x next = lookup_var x cc) /\
    next.vs_allocas = cc.vs_allocas /\
    (!fuel rr. run_from fuel ctx func next = rr /\ (!e. rr <> Error e) ==>
       ?fuel'. run_from fuel' ctx func cc = rr)
Proof
  rpt gen_tac >> strip_tac >>
  `k <= n` by fs[array_loop_inv_def] >>
  `(n2w k : bytes32) = n2w n <=> k = n` by
    (`k < dimword (:256)` by decide_tac >> simp[n2w_11]) >>
  qexists_tac `jump_to (if k = n then exit_lbl else stmts_lbl)
    (update_var dv (bool_to_word (k = n)) cc)` >>
  conj_tac
  >- (fs[array_loop_inv_def, lookup_var_def] >>
      `stmt_state_rel ctx func cenv cx es
         (update_var dv (bool_to_word (k = LENGTH vs)) cc)` by
        (irule stmt_state_rel_update_var >> simp[]) >>
      fs[stmt_state_rel_jump_to, jump_to_def, update_var_def,
           lookup_var_def, FLOOKUP_UPDATE] >>
      conj_tac
      >- (Cases_on `saved_base` >>
          gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
      fs[ret_pc_ok_def] >> rpt strip_tac >>
      first_x_assum drule >> strip_tac >> simp[] >>
      Cases_on `x = dv` >> gvs[lookup_var_def, FLOOKUP_UPDATE]) >>
  conj_tac >- simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[jump_to_def, update_var_def] >>
  fs[array_loop_inv_def] >> drule array_condition_block >>
  simp[] >> disch_then (qspecl_then [`ctx`, `cc`, `n2w k`] mp_tac) >>
  gvs[n2w_11]
QED

Theorem array_ret_pc_update[local]:
  ret_pc_ok cenv st s ==> ret_pc_ok cenv st (update_var v w s)
Proof
  rw[ret_pc_ok_def] >> first_x_assum drule >> strip_tac >> simp[] >>
  Cases_on `x = v` >> gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem array_increment_boundary:
  !ctx func cenv cx P vs id idx saved_base base p dst sz ainst cond_lbl
   incr_lbl st k es dd nv i1 i2 i3.
  lookup_block incr_lbl func.fn_blocks =
    SOME <| bb_label := incr_lbl;
            bb_instructions :=
              [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
               mk_inst i2 ASSIGN [Var nv] [idx];
               mk_inst i3 JMP [Label cond_lbl] []] |> /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base base p dst sz
    ainst incr_lbl st k es dd /\ k < LENGTH vs /\
  not_local_ptr cenv es.scopes idx /\ not_local_ptr cenv es.scopes nv /\
  p <> idx /\ p <> nv /\
  (!x. saved_base = Var x ==> x <> idx /\ x <> nv) ==>
  ?next.
    array_loop_inv ctx func cenv cx P vs id idx saved_base base p dst sz
      ainst cond_lbl st (k+1) es next /\
    (!x. x <> idx /\ x <> nv ==> lookup_var x next = lookup_var x dd) /\
    next.vs_allocas = dd.vs_allocas /\
    (!fuel rr. run_from fuel ctx func next = rr /\ (!e. rr <> Error e) ==>
       ?fuel'. run_from fuel' ctx func dd = rr)
Proof
  rpt gen_tac >> strip_tac >>
  qexists_tac `jump_to cond_lbl
    (update_var idx (n2w k + 1w) (update_var nv (n2w k + 1w) dd))` >>
  conj_tac
  >- (fs[array_loop_inv_def] >>
      `stmt_state_rel ctx func cenv cx es
        (update_var idx (n2w k + 1w) (update_var nv (n2w k + 1w) dd))` by
        (irule stmt_state_rel_update_var >> simp[] >>
         irule stmt_state_rel_update_var >> simp[]) >>
      `ret_pc_ok cenv st
        (update_var idx (n2w k + 1w) (update_var nv (n2w k + 1w) dd))` by
        (irule array_ret_pc_update >> irule array_ret_pc_update >> simp[]) >>
      fs[stmt_state_rel_jump_to, ret_pc_ok_jump_to] >>
      fs[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
         word_add_n2w] >>
      Cases_on `saved_base` >>
      gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  conj_tac >- simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[jump_to_def, update_var_def] >>
  fs[array_loop_inv_def] >> drule stmtSimForPartsTheory.for_incr_block >>
  simp[] >> disch_then (qspecl_then [`ctx`, `dd`, `n2w k`] mp_tac) >> simp[]
QED

Theorem array_address_prefix_run:
  !s idx saved_base arr_base k stride ov ep j3 j4.
  lookup_var idx s = SOME (n2w k) /\
  eval_operand saved_base s = SOME arr_base /\
  (!x. saved_base = Var x ==> x <> ov) ==>
  run_inst_seq
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [saved_base; Var ov] [ep]] s =
  OK (update_var ep (n2w (w2n arr_base + k * stride))
        (update_var ov (n2w (k * stride)) s))
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]) s =
   OK (update_var ov (n2w (k * stride)) s)` by
    (simp[GSYM word_mul_n2w] >> irule step_MUL >> simp[eval_operand_def]) >>
  `eval_operand saved_base (update_var ov (n2w (k * stride)) s) = SOME arr_base` by
    (Cases_on `saved_base` >>
     gvs[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `step_inst_base (mk_inst j4 ADD [saved_base; Var ov] [ep])
     (update_var ov (n2w (k * stride)) s) =
   OK (update_var ep (arr_base + n2w (k * stride))
        (update_var ov (n2w (k * stride)) s))` by
    (irule step_ADD >> simp[eval_operand_def, update_var_def,
                            lookup_var_def, FLOOKUP_UPDATE]) >>
  simp[run_inst_seq_def, GSYM word_add_n2w, n2w_w2n]
QED

Theorem array_address_prefix_boundary:
  !ctx func cenv cx es s idx saved_base arr_base k stride ov ep j3 j4 st.
  lookup_var idx s = SOME (n2w k) /\
  eval_operand saved_base s = SOME arr_base /\
  (!x. saved_base = Var x ==> x <> ov) /\
  stmt_state_rel ctx func cenv cx es s /\ ret_pc_ok cenv st s /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes ep ==>
  ?s1. run_inst_seq
      [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
       mk_inst j4 ADD [saved_base; Var ov] [ep]] s = OK s1 /\
    stmt_state_rel ctx func cenv cx es s1 /\ ret_pc_ok cenv st s1 /\
    lookup_var ep s1 = SOME (n2w (w2n arr_base + k * stride)) /\
    (s1 with vs_vars := s.vs_vars) = s /\
    (!x. x <> ov /\ x <> ep ==> lookup_var x s1 = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all array_address_prefix_run >>
  disch_then (qspecl_then [`stride`, `ep`, `j3`, `j4`] assume_tac) >>
  qexists_tac `update_var ep (n2w (w2n arr_base + k * stride))
    (update_var ov (n2w (k * stride)) s)` >> simp[] >>
  conj_tac
  >- (irule stmt_state_rel_update_var >> simp[] >>
      irule stmt_state_rel_update_var >> simp[]) >>
  conj_tac
  >- (irule array_ret_pc_update >> irule array_ret_pc_update >> simp[]) >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem array_for_code_copy_reserved:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj ==>
  local_ptrs_reserved bc sa
Proof
  simp[array_for_code_def]
QED

Theorem array_copy_live_ptrs_reserved:
  local_ptrs_reserved bc sa /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) ==>
  !q. q = p \/ ~not_local_ptr bc scopes q ==> not_fresh_at sa q
Proof
  simp[local_ptrs_reserved_def, not_local_ptr_def] >> metis_tac[]
QED

Theorem array_empty_scope_ptr_transport:
  cenv_top_ext cenv bc (FEMPTY :: scopes) ==>
  (not_local_ptr bc (FEMPTY :: scopes) q <=> not_local_ptr cenv scopes q)
Proof
  strip_tac >>
  `!name entry. lookup_scopes name scopes = SOME entry ==>
      FLOOKUP bc.ce_vars name = FLOOKUP cenv.ce_vars name` by
    (rpt strip_tac >> spose_not_then assume_tac >>
     fs[cenv_top_ext_def] >> first_x_assum drule >> simp[]) >>
  `bc.ce_imm_alloca = cenv.ce_imm_alloca` by
    fs[cenv_top_ext_def, compile_env_component_equality] >>
  simp[not_local_ptr_def, lookup_scopes_def] >> metis_tac[]
QED

Theorem array_copy_run_declare:
  !ctx func cenv cx es s id p sz dw inst v tv sc rest a sa sb src ty tenv sw.
  compile_iter_elem_copy cenv src (Var p) (type_memory_size tv)
    LocMemory F ty ty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  local_ptrs_reserved cenv sa /\
  eval_operand src s = SOME sw /\ lookup_var p s = SOME dw /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  val_in_memory tv v (w2n sw) s.vs_memory /\
  type_memory_size tv + 64 < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr cenv es.scopes p /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [p] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,sz) /\
  type_memory_size tv <= sz ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx
      (es with scopes :=
        (sc |+ (id, <|assignable := a; type := tv; value := v; popped := []|>)) :: rest) t /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  `!q. q = p \/ ~not_local_ptr cenv es.scopes q ==> not_fresh_at sa q` by
    metis_tac[array_copy_live_ptrs_reserved] >>
  `not_fresh_at sa p` by metis_tac[] >>
  `eval_operand (Var p) s = SOME dw` by simp[eval_operand_def] >>
  `!x. Var p = Var x ==> not_fresh_at sa x` by simp[] >>
  drule_all array_iter_copy_run >> strip_tac >>
  drule_all array_iter_copy_declare_rel >>
  disch_then (qspec_then `a` assume_tac) >>
  qexists_tac `t` >> simp[]
QED

Theorem array_seq_prefix_result:
  !ctx func s t bb insts.
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX insts (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) insts /\
  run_inst_seq insts s = OK t /\ ~s.vs_halted /\ ~t.vs_halted ==>
  !fuel. run_from fuel ctx func s =
    run_from fuel ctx func (t with vs_inst_idx := s.vs_inst_idx + LENGTH insts)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  drule_all exec_block_run_inst_seq >>
  disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >>
  strip_tac >> first_x_assum drule >> strip_tac >> simp[run_from_def]
QED

Theorem array_empty_scope_rel_transport:
  !ctx func cenv bc cx es s.
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\
  stmt_state_rel ctx func cenv cx es s ==>
  stmt_state_rel ctx func bc cx (es with scopes := FEMPTY :: es.scopes) s
Proof
  rpt gen_tac >> strip_tac >>
  `!name entry. lookup_scopes name es.scopes = SOME entry ==>
      FLOOKUP bc.ce_vars name = FLOOKUP cenv.ce_vars name` by
    (rpt strip_tac >> spose_not_then assume_tac >>
     fs[cenv_top_ext_def] >> first_x_assum drule >> simp[]) >>
  irule stmt_state_rel_cenv_cong >> qexists_tac `cenv` >>
  simp[stmt_state_rel_push_scope, lookup_scopes_def] >>
  fs[cenv_top_ext_def] >>
  qpat_x_assum `_ with <|ce_vars := _; ce_dynarray_capacity := _;
    ce_var_type := _|> = _` (SUBST1_TAC o SYM) >> simp[]
QED

Theorem array_for_body_entry_run:
  !ctx func cenv bc cx es s id p sz dst ainst tv v et tenv sa sb0
   idx saved_base arr_base k stride ov ep j3 j4.
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocMemory F et et sa = ((),sb0) /\
  stride = type_memory_size tv /\ type_memory_bytes cenv et = stride /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n arr_base + k * stride) s.vs_memory /\
  w2n arr_base + k * stride < dimword (:256) /\ stride + 64 < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\ local_ptrs_reserved bc sa /\
  lookup_scopes id es.scopes = NONE /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes ep /\
  lookup_var idx s = SOME (n2w k) /\ eval_operand saved_base s = SOME arr_base /\
  lookup_var p s = SOME dst /\ p <> ov /\ p <> ep /\
  (!x. saved_base = Var x ==> x <> ov) /\
  not_fresh_at sa ep /\
  MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
  ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\ stride <= sz ==>
  ?t. run_inst_seq
    ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
      mk_inst j4 ADD [saved_base; Var ov] [ep]] ++ emitted_insts sa sb0) s = OK t /\
    stmt_state_rel ctx func bc cx
      (es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes) t /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x /\ x <> ov /\ x <> ep ==>
      lookup_var x t = lookup_var x s) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb0)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `s1 = update_var ep (n2w (w2n arr_base + k * stride))
    (update_var ov (n2w (k * stride)) s)` >>
  `run_inst_seq [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [saved_base; Var ov] [ep]] s = OK s1` by
    (simp[Abbr `s1`] >> irule array_address_prefix_run >> simp[] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx es s1` by
    (simp[Abbr `s1`] >> irule stmt_state_rel_update_var >> simp[] >>
     irule stmt_state_rel_update_var >> simp[]) >>
  `stmt_state_rel ctx func bc cx (es with scopes := FEMPTY :: es.scopes) s1` by
    (irule array_empty_scope_rel_transport >> qexists_tac `cenv` >> simp[]) >>
  `not_fresh_at sa p` by metis_tac[array_copy_live_ptrs_reserved] >>
  `!x. Var ep = Var x ==> not_fresh_at sa x` by simp[] >>
  `!x. Var p = Var x ==> not_fresh_at sa x` by simp[] >>
  `eval_operand (Var ep) s1 = SOME (n2w (w2n arr_base + k * stride)) /\
   eval_operand (Var p) s1 = SOME dst` by
    fs[Abbr `s1`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `val_in_memory tv v (w2n (n2w (w2n arr_base + k * stride) : bytes32)) s1.vs_memory` by
    gvs[Abbr `s1`, update_var_def, w2n_n2w] >>
  `type_memory_bytes cenv et = type_memory_size tv /\
   type_memory_size tv + 64 < dimword (:256)` by metis_tac[] >>
  drule_all array_iter_copy_run >> strip_tac >>
  `lookup_var p s1 = SOME dst /\
   FLOOKUP s1.vs_allocas ainst.inst_id = SOME (w2n dst,sz)` by
    (qpat_x_assum `lookup_var p s = SOME dst` mp_tac >>
     simp[Abbr `s1`, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `(es with scopes := FEMPTY :: es.scopes).scopes = FEMPTY :: es.scopes /\
   lookup_scopes id (es with scopes := FEMPTY :: es.scopes).scopes = NONE /\
   not_local_ptr bc (es with scopes := FEMPTY :: es.scopes).scopes p /\
   type_memory_size tv <= sz` by (simp[lookup_scopes_def] >> gvs[]) >>
  `!q. q = p \/ ~not_local_ptr bc (es with scopes := FEMPTY :: es.scopes).scopes q ==>
    not_fresh_at sa q` by metis_tac[array_copy_live_ptrs_reserved] >>
  drule_all array_iter_copy_declare_rel >>
  disch_then (qspec_then `F` mp_tac) >>
  simp[lookup_scopes_def] >> strip_tac >>
  qexists_tac `t` >> conj_tac
  >- (qpat_assum `run_inst_seq [_;_] s = OK s1`
        (mp_then Any (qspec_then `emitted_insts sa sb0` mp_tac) run_inst_seq_append) >>
      gvs[]) >>
  simp[] >> conj_tac
  >- (qpat_x_assum `(t with <|vs_vars := _; vs_memory := _|>) = s1` mp_tac >>
      simp[Abbr `s1`, update_var_def] >>
      POP_ASSUM_LIST (K all_tac) >>
      simp[venom_state_component_equality] >> strip_tac >> gvs[]) >>
  rpt strip_tac >> first_x_assum drule >>
  simp[Abbr `s1`, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem array_body_prefix_continuation:
  !ctx func cenv cx es s t sb bb insts.
  lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb.cs_current_insts bb.bb_instructions /\
  insts = sb.cs_current_insts /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  run_inst_seq insts s = OK t /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) insts /\
  stmt_state_rel ctx func cenv cx es t /\
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s ==>
  ?s2. s2.vs_current_bb = sb.cs_current_bb /\
    s2.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~s2.vs_halted /\
    stmt_state_rel ctx func cenv cx es s2 /\
    s2.vs_vars = t.vs_vars /\ s2.vs_allocas = s.vs_allocas /\
    (!fuel. run_from fuel ctx func s = run_from fuel ctx func s2)
Proof
  rpt gen_tac >> strip_tac >>
  `t.vs_current_bb = s.vs_current_bb /\ t.vs_allocas = s.vs_allocas /\
   t.vs_halted = s.vs_halted` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = _` mp_tac >>
     simp[venom_state_component_equality]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx] >>
  `isPREFIX insts (DROP s.vs_inst_idx bb.bb_instructions) /\
   lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\ ~t.vs_halted` by simp[] >>
  drule_all array_seq_prefix_result >> simp[]
QED

Theorem array_ret_pc_copy_frame[local]:
  ret_pc_ok bc st s /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
  (!x. not_fresh_at sa x /\ x <> ov /\ x <> ep ==>
    lookup_var x t = lookup_var x s) ==>
  ret_pc_ok bc st t
Proof
  rw[ret_pc_ok_def] >>
  `not_fresh_at sa x /\ x <> ov /\ x <> ep` by metis_tac[] >>
  first_x_assum drule >> simp[] >> metis_tac[]
QED

Theorem array_for_body_entry:
  !ctx func cenv bc cx es s id p sz dst ainst tv v et tenv sa sb0
   idx saved_base arr_base k stride ov ep j3 j4 bb st.
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocMemory F et et sa = ((),sb0) /\
  stride = type_memory_size tv /\ type_memory_bytes cenv et = stride /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n arr_base + k * stride) s.vs_memory /\
  w2n arr_base + k * stride < dimword (:256) /\ stride + 64 < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\ local_ptrs_reserved bc sa /\
  lookup_scopes id es.scopes = NONE /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes ep /\
  lookup_var idx s = SOME (n2w k) /\ eval_operand saved_base s = SOME arr_base /\
  lookup_var p s = SOME dst /\ p <> ov /\ p <> ep /\
  (!x. saved_base = Var x ==> x <> ov) /\ not_fresh_at sa ep /\
  MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
  ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\ stride <= sz /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  sb0.cs_current_insts =
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [saved_base; Var ov] [ep]] ++ emitted_insts sa sb0 /\
  s.vs_current_bb = sb0.cs_current_bb /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  ret_pc_ok bc st s /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) ==>
  ?s2. s2.vs_current_bb = sb0.cs_current_bb /\
    s2.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ~s2.vs_halted /\
    stmt_state_rel ctx func bc cx
      (es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes) s2 /\
    ret_pc_ok bc st s2 /\ s2.vs_allocas = s.vs_allocas /\
    (!x. not_fresh_at sa x /\ x <> ov /\ x <> ep ==>
      lookup_var x s2 = lookup_var x s) /\
    (!fuel. run_from fuel ctx func s = run_from fuel ctx func s2)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all array_for_body_entry_run >>
  disch_then (qspecl_then [`j3`, `j4`] strip_assume_tac) >>
  `run_inst_seq sb0.cs_current_insts s = OK t` by metis_tac[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    sb0.cs_current_insts` by
    simp[mk_inst_def, is_terminator_def] >>
  `sb0.cs_current_insts = sb0.cs_current_insts` by simp[] >>
  drule_all array_body_prefix_continuation >> strip_tac >>
  `ret_pc_ok bc st t` by (irule array_ret_pc_copy_frame >> metis_tac[]) >>
  qexists_tac `s2` >> simp[] >>
  `!x. lookup_var x s2 = lookup_var x t` by simp[lookup_var_def] >>
  conj_tac
  >- (fs[ret_pc_ok_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem array_body_scope_projection:
  !ctx func cenv bc c3 cx ei stmts r es2 s sc rest.
  cenv_top_ext cenv bc ei.scopes /\
  eval_stmts cx stmts ei = (r,es2) /\
  cenv_top_ext bc c3 es2.scopes /\
  stmt_state_rel ctx func c3 cx es2 s /\ es2.scopes = sc :: rest /\
  (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) ==>
  stmt_state_rel ctx func cenv cx (es2 with scopes := rest) s
Proof
  rpt gen_tac >> strip_tac >>
  drule eval_stmts_preserves_scopes_dom >> strip_tac >>
  `cenv_top_ext cenv c3 es2.scopes` by
    (irule cenv_top_ext_trans >> qexistsl_tac [`bc`, `ei.scopes`] >>
     gvs[preserves_scopes_dom_def]) >>
  drule_all stmt_state_rel_pop_top_ext >> simp[]
QED

Theorem array_body_fragment_run:
  !ctx func cx lctx RetQ cenv bc m ei stmts r es2 sa sb s0 cenv' sc rest.
  stmt_frag ctx func cx lctx RetQ bc m (eval_stmts cx stmts) ei /\
  m sa = (cenv',sb) /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved bc sa /\ ret_pc_ok bc sa s0 /\
  ~block_is_terminated sa /\ stmt_res_ok lctx r /\
  stmt_state_rel ctx func bc cx ei s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  cenv_top_ext cenv bc ei.scopes /\ eval_stmts cx stmts ei = (r,es2) /\
  es2.scopes = sc :: rest /\
  (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) ==>
  (?s. stmt_lands lctx sb r s /\ ~s.vs_halted /\
    (r = INL () ==> ~block_is_terminated sb) /\
    stmt_state_rel ctx func cenv cx (es2 with scopes := rest) s /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
      lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
      FLOOKUP s.vs_allocas aid = SOME b) /\
    (!fuel rr. run_from fuel ctx func s = rr /\ (!e. rr <> Error e) ==>
      ?fuel'. run_from fuel' ctx func s0 = rr)) \/
  (?fuel rr. run_from fuel ctx func s0 = rr /\ exit_result rr /\
    stmt_exit RetQ (es2 with scopes := rest) r rr)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_frag _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[stmt_frag_def] >>
  disch_then (qspecl_then [`sa`, `sb`, `s0`, `cenv'`] mp_tac) >>
  simp[] >> strip_tac
  >- (disj1_tac >> rename1 `stmt_state_rel ctx func c3 cx es2 s3` >>
      `cenv_top_ext bc c3 es2.scopes` by simp[] >>
      `stmt_state_rel ctx func cenv cx (es2 with scopes := rest) s3` by
        (drule_all array_body_scope_projection >> simp[]) >>
      qexists_tac `s3` >> simp[]) >>
  disj2_tac >> rename1 `run_from fu ctx func s0 = result` >>
  qexists_tac `fu` >> fs[stmt_exit_def]
QED

Theorem array_body_to_increment:
  !ctx func cenv cx es s r sb sj exit_lbl incr_lbl.
  stmt_lands (InLoop exit_lbl incr_lbl) sb r s /\
  (r = INL () \/ r = INR ContinueException) /\ ~s.vs_halted /\
  stmt_state_rel ctx func cenv cx es s /\
  (r = INL () ==>
    sj.cs_blocks = sb.cs_blocks /\ sj.cs_current_bb = sb.cs_current_bb /\
    sj.cs_current_insts = sb.cs_current_insts ++
      [mk_inst sb.cs_next_id JMP [Label incr_lbl] []] /\
    fn_has_code sb sj func) ==>
  ?dd. dd.vs_current_bb = incr_lbl /\ dd.vs_inst_idx = 0 /\ ~dd.vs_halted /\
    stmt_state_rel ctx func cenv cx es dd /\
    dd.vs_vars = s.vs_vars /\ dd.vs_allocas = s.vs_allocas /\
    (!fuel rr. run_from fuel ctx func dd = rr /\ (!e. rr <> Error e) ==>
      ?fuel'. run_from fuel' ctx func s = rr)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `r = INL ()`
  >- (gvs[stmt_lands_def] >>
      qexists_tac `jump_to incr_lbl s` >>
      simp[stmt_state_rel_jump_to, jump_to_def] >>
      `is_terminator (mk_inst sb.cs_next_id JMP [Label incr_lbl] []).inst_opcode /\
       (mk_inst sb.cs_next_id JMP [Label incr_lbl] []).inst_opcode <> INVOKE /\
       step_inst_base (mk_inst sb.cs_next_id JMP [Label incr_lbl] []) s =
         OK (jump_to incr_lbl s)` by
        simp[mk_inst_def, is_terminator_def, step_jmp_behavior] >>
      drule_at (Pat `fn_has_code _ _ _`) run_from_jump_end >>
      disch_then (qspecl_then [`ctx`, `s`,
        `mk_inst sb.cs_next_id JMP [Label incr_lbl] []`, `incr_lbl`] mp_tac) >>
      simp[jump_to_def]) >>
  gvs[stmt_lands_def] >> qexists_tac `s` >> simp[] >> metis_tac[]
QED

Theorem array_body_break_lands:
  stmt_lands (InLoop exit_lbl incr_lbl) sb (INR BreakException) s ==>
  s.vs_current_bb = exit_lbl /\ s.vs_inst_idx = 0
Proof
  simp[stmt_lands_def]
QED

Theorem array_body_exit_pullback:
  (!fuel rr. run_from fuel ctx func s2 = rr /\ (!e. rr <> Error e) ==>
    ?fuel'. run_from fuel' ctx func cc = rr) /\
  run_from fuel ctx func s2 = rr /\ exit_result rr /\
  stmt_exit RetQ es r rr ==>
  ?fuel'. run_from fuel' ctx func cc = rr /\ exit_result rr /\ stmt_exit RetQ es r rr
Proof
  rpt strip_tac >> `!e. rr <> Error e` by (Cases_on `rr` >> fs[exit_result_def]) >>
  first_x_assum drule_all >> strip_tac >> metis_tac[]
QED

Theorem array_saved_operand_frame:
  (!l. op <> Label l) /\ eval_operand op s = SOME w /\
  (!x. op = Var x ==> lookup_var x t = lookup_var x s) ==>
  eval_operand op t = SOME w
Proof
  Cases_on `op` >> simp[eval_operand_def] >> metis_tac[]
QED

Theorem array_body_runtime_frame:
  !cenv bc scopes sa s0 st idx k p dst saved_base base ainst sz s.
  cenv_top_ext cenv bc scopes /\ ret_pc_ok bc sa s0 /\
  ret_pc_ok cenv st s0 /\
  lookup_var idx s0 = SOME (n2w k) /\
  lookup_var p s0 = SOME dst /\ eval_operand saved_base s0 = SOME base /\
  FLOOKUP s0.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
  not_fresh_at sa idx /\ not_fresh_at sa p /\
  (!x. saved_base = Var x ==> not_fresh_at sa x) /\
  (!l. saved_base <> Label l) /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
    lookup_var x s = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
    FLOOKUP s.vs_allocas aid = SOME b) ==>
  lookup_var idx s = SOME (n2w k) /\ lookup_var p s = SOME dst /\
  eval_operand saved_base s = SOME base /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
  ret_pc_ok cenv st s
Proof
  rpt strip_tac
  >- metis_tac[]
  >- metis_tac[]
  >- (irule array_saved_operand_frame >> conj_tac >- simp[] >>
      qexists_tac `s0` >> simp[] >>
      Cases_on `saved_base` >> gvs[eval_operand_def] >> metis_tac[])
  >- metis_tac[] >>
  fs[ret_pc_ok_def, cenv_top_ext_def] >>
  `bc.ce_return_pc = cenv.ce_return_pc` by
    (qpat_x_assum `_ with <|ce_vars := _; ce_dynarray_capacity := _;
       ce_var_type := _|> = _` mp_tac >>
     simp[compile_env_component_equality]) >>
  metis_tac[]
QED

Theorem array_body_continue_iteration_framed[local]:
  !ctx func cenv cx P vs id idx saved_base arr_base p dst sz ainst st k es s
   r sb sj exit_lbl incr_lbl cond_lbl nv i1 i2 i3 cc.
  stmt_lands (InLoop exit_lbl incr_lbl) sb r s /\
  (r = INL () \/ r = INR ContinueException) /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst s.vs_current_bb st k es (s with vs_inst_idx := 0) /\
  (!l. saved_base <> Label l) /\ k < LENGTH vs /\
  (r = INL () ==>
    sj.cs_blocks = sb.cs_blocks /\ sj.cs_current_bb = sb.cs_current_bb /\
    sj.cs_current_insts = sb.cs_current_insts ++
      [mk_inst sb.cs_next_id JMP [Label incr_lbl] []] /\ fn_has_code sb sj func) /\
  lookup_block incr_lbl func.fn_blocks =
    SOME <|bb_label := incr_lbl; bb_instructions :=
      [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
       mk_inst i2 ASSIGN [Var nv] [idx];
       mk_inst i3 JMP [Label cond_lbl] []]|> /\
  not_local_ptr cenv es.scopes idx /\ not_local_ptr cenv es.scopes nv /\
  p <> idx /\ p <> nv /\
  (!x. saved_base = Var x ==> x <> idx /\ x <> nv) /\
  (!fuel rr. run_from fuel ctx func s = rr /\ (!e. rr <> Error e) ==>
    ?fuel'. run_from fuel' ctx func cc = rr) ==>
  ?next. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond_lbl st (k+1) es next /\
    (!x. x <> idx /\ x <> nv ==> lookup_var x next = lookup_var x s) /\
    next.vs_allocas = s.vs_allocas /\
    (!fuel rr. run_from fuel ctx func next = rr /\ (!e. rr <> Error e) ==>
      ?fuel'. run_from fuel' ctx func cc = rr)
Proof
  rpt gen_tac >> strip_tac >>
  `~s.vs_halted /\ stmt_state_rel ctx func cenv cx es s` by
    fs[array_loop_inv_def, stmt_state_rel_inst_idx] >>
  drule array_body_to_increment >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `sj`] mp_tac) >>
  simp[] >> strip_tac >>
  `array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst incr_lbl st k es dd` by
    (gvs[array_loop_inv_def, stmt_state_rel_inst_idx, ret_pc_ok_def,
         lookup_var_def] >>
     Cases_on `saved_base` >> gvs[eval_operand_def, lookup_var_def]) >>
  drule_all array_increment_boundary >> strip_tac >>
  qexists_tac `next` >> simp[lookup_var_def] >> metis_tac[]
QED

Theorem array_body_continue_iteration[local]:
  !ctx func cenv cx P vs id idx saved_base base p dst sz ainst st k es s
   r sb sj exit_lbl incr_lbl cond_lbl nv i1 i2 i3 cc.
  stmt_lands (InLoop exit_lbl incr_lbl) sb r s /\
  (r = INL () \/ r = INR ContinueException) /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base base p dst sz
    ainst s.vs_current_bb st k es (s with vs_inst_idx := 0) /\
  (!l. saved_base <> Label l) /\ k < LENGTH vs /\
  (r = INL () ==>
    sj.cs_blocks = sb.cs_blocks /\ sj.cs_current_bb = sb.cs_current_bb /\
    sj.cs_current_insts = sb.cs_current_insts ++
      [mk_inst sb.cs_next_id JMP [Label incr_lbl] []] /\ fn_has_code sb sj func) /\
  lookup_block incr_lbl func.fn_blocks =
    SOME <|bb_label := incr_lbl; bb_instructions :=
      [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
       mk_inst i2 ASSIGN [Var nv] [idx];
       mk_inst i3 JMP [Label cond_lbl] []]|> /\
  not_local_ptr cenv es.scopes idx /\ not_local_ptr cenv es.scopes nv /\
  p <> idx /\ p <> nv /\
  (!x. saved_base = Var x ==> x <> idx /\ x <> nv) /\
  (!fuel rr. run_from fuel ctx func s = rr /\ (!e. rr <> Error e) ==>
    ?fuel'. run_from fuel' ctx func cc = rr) ==>
  ?next. array_loop_inv ctx func cenv cx P vs id idx saved_base base p dst sz
    ainst cond_lbl st (k+1) es next /\
    (!fuel rr. run_from fuel ctx func next = rr /\ (!e. rr <> Error e) ==>
      ?fuel'. run_from fuel' ctx func cc = rr)
Proof
  rpt gen_tac >>
  disch_then (strip_assume_tac o MATCH_MP array_body_continue_iteration_framed) >>
  metis_tac[]
QED

(* The execution proof retains every old non-counter register.  The public
   caller-frame theorem specializes this scratch-exclusion interface. *)
Theorem array_for_iteration_frames[local]:
  !ctx func cx RetQ cenv bc m ei stmts r es2 sa sb s2 cenv' sc rest
   idx k p dst saved_base arr_base ainst sz st P vs id sj exit_lbl incr_lbl
   cond_lbl nv i1 i2 i3 cc.
  stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc m (eval_stmts cx stmts) ei /\
  m sa = (cenv',sb) /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved bc sa /\ ret_pc_ok bc sa s2 /\
  ~block_is_terminated sa /\ stmt_res_ok (InLoop exit_lbl incr_lbl) r /\
  stmt_state_rel ctx func bc cx ei s2 /\ ~s2.vs_halted /\
  s2.vs_current_bb = sa.cs_current_bb /\
  s2.vs_inst_idx = LENGTH sa.cs_current_insts /\
  cenv_top_ext cenv bc ei.scopes /\ eval_stmts cx stmts ei = (r,es2) /\
  es2.scopes = sc :: rest /\
  (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) /\
  lookup_var idx s2 = SOME (n2w k) /\ eval_operand saved_base s2 = SOME arr_base /\
  lookup_var p s2 = SOME dst /\
  FLOOKUP s2.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
  ret_pc_ok cenv st s2 /\ not_fresh_at sa idx /\ not_fresh_at sa p /\
  (!x. saved_base = Var x ==> not_fresh_at sa x) /\
  (!l. saved_base <> Label l) /\ k < LENGTH vs /\
  (r = INL () \/ r = INR ContinueException ==>
    P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE) /\
  (r = INL () ==>
    sj.cs_blocks = sb.cs_blocks /\ sj.cs_current_bb = sb.cs_current_bb /\
    sj.cs_current_insts = sb.cs_current_insts ++
      [mk_inst sb.cs_next_id JMP [Label incr_lbl] []] /\ fn_has_code sb sj func) /\
  lookup_block incr_lbl func.fn_blocks =
    SOME <|bb_label := incr_lbl; bb_instructions :=
      [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
       mk_inst i2 ASSIGN [Var nv] [idx];
       mk_inst i3 JMP [Label cond_lbl] []]|> /\
  not_local_ptr cenv rest idx /\ not_local_ptr cenv rest nv /\
  p <> idx /\ p <> nv /\
  (!x. saved_base = Var x ==> x <> idx /\ x <> nv) /\
  (!fuel rr. run_from fuel ctx func s2 = rr /\ (!e. rr <> Error e) ==>
    ?fuel'. run_from fuel' ctx func cc = rr) ==>
  ((r = INL () \/ r = INR ContinueException) /\
   ?next. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst cond_lbl st (k+1) (es2 with scopes := rest) next /\
     (!x w. not_fresh_at sa x /\ x <> idx /\ x <> nv /\
       lookup_var x s2 = SOME w ==> lookup_var x next = SOME w) /\
     (!aid b. FLOOKUP s2.vs_allocas aid = SOME b ==>
       FLOOKUP next.vs_allocas aid = SOME b) /\
     (!fuel rr. run_from fuel ctx func next = rr /\ (!e. rr <> Error e) ==>
       ?fuel'. run_from fuel' ctx func cc = rr)) \/
  (r = INR BreakException /\
   ?next. next.vs_current_bb = exit_lbl /\ next.vs_inst_idx = 0 /\
     ~next.vs_halted /\
     stmt_state_rel ctx func cenv cx (es2 with scopes := rest) next /\
     (!x w. not_fresh_at sa x /\ x <> idx /\ x <> nv /\
       lookup_var x s2 = SOME w ==> lookup_var x next = SOME w) /\
     (!aid b. FLOOKUP s2.vs_allocas aid = SOME b ==>
       FLOOKUP next.vs_allocas aid = SOME b) /\
     (!fuel rr. run_from fuel ctx func next = rr /\ (!e. rr <> Error e) ==>
       ?fuel'. run_from fuel' ctx func cc = rr)) \/
  (?fuel rr. run_from fuel ctx func cc = rr /\ exit_result rr /\
    stmt_exit RetQ (es2 with scopes := rest) r rr)
Proof
  rpt gen_tac >> strip_tac >> drule_all array_body_fragment_run >> strip_tac
  >- (`!fuel rr. run_from fuel ctx func s = rr /\ (!e. rr <> Error e) ==>
         ?fuel'. run_from fuel' ctx func cc = rr` by metis_tac[] >>
      Cases_on `r = INR BreakException`
      >- (disj2_tac >> disj1_tac >> simp[] >> qexists_tac `s` >>
          fs[stmt_lands_def] >> metis_tac[]) >>
      `r = INL () \/ r = INR ContinueException` by fs[stmt_lands_def] >>
      drule_all array_body_runtime_frame >> strip_tac >>
      `array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
         ainst s.vs_current_bb st k (es2 with scopes := rest)
         (s with vs_inst_idx := 0)` by
        (simp[array_loop_inv_def, stmt_state_rel_inst_idx, lookup_var_def,
              ret_pc_ok_def] >>
         Cases_on `saved_base` >> gvs[eval_operand_def, lookup_var_def, ret_pc_ok_def]) >>
      `?next. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
         ainst cond_lbl st (k+1) (es2 with scopes := rest) next /\
         (!x. x <> idx /\ x <> nv ==> lookup_var x next = lookup_var x s) /\
         next.vs_allocas = s.vs_allocas /\
         (!fuel rr. run_from fuel ctx func next = rr /\ (!e. rr <> Error e) ==>
           ?fuel'. run_from fuel' ctx func cc = rr)` by
        (irule array_body_continue_iteration_framed >> simp[] >>
         (conj_tac >- metis_tac[]) >>
         goal_assum (drule_at (Pat `lookup_block _ _ = _`)) >>
         goal_assum (drule_at (Pat `stmt_lands _ _ _ _`)) >>
         qexists_tac `sj` >> simp[]) >>
      disj1_tac >> simp[] >> qexists_tac `next` >> simp[] >> metis_tac[]) >>
  disj2_tac >> disj2_tac >> drule_all array_body_exit_pullback >> metis_tac[]
QED

Theorem array_for_iteration:
  !ctx func cx RetQ cenv bc m ei stmts r es2 sa sb s2 cenv' sc rest
   idx k p dst saved_base arr_base ainst sz st P vs id sj exit_lbl incr_lbl
   cond_lbl nv i1 i2 i3 cc.
  stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc m (eval_stmts cx stmts) ei /\
  m sa = (cenv',sb) /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved bc sa /\ ret_pc_ok bc sa s2 /\
  ~block_is_terminated sa /\ stmt_res_ok (InLoop exit_lbl incr_lbl) r /\
  stmt_state_rel ctx func bc cx ei s2 /\ ~s2.vs_halted /\
  s2.vs_current_bb = sa.cs_current_bb /\
  s2.vs_inst_idx = LENGTH sa.cs_current_insts /\
  cenv_top_ext cenv bc ei.scopes /\ eval_stmts cx stmts ei = (r,es2) /\
  es2.scopes = sc :: rest /\
  (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) /\
  lookup_var idx s2 = SOME (n2w k) /\ eval_operand saved_base s2 = SOME arr_base /\
  lookup_var p s2 = SOME dst /\
  FLOOKUP s2.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
  ret_pc_ok cenv st s2 /\ not_fresh_at sa idx /\ not_fresh_at sa p /\
  (!x. saved_base = Var x ==> not_fresh_at sa x) /\
  (!l. saved_base <> Label l) /\ k < LENGTH vs /\
  (r = INL () \/ r = INR ContinueException ==>
    P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE) /\
  (r = INL () ==>
    sj.cs_blocks = sb.cs_blocks /\ sj.cs_current_bb = sb.cs_current_bb /\
    sj.cs_current_insts = sb.cs_current_insts ++
      [mk_inst sb.cs_next_id JMP [Label incr_lbl] []] /\ fn_has_code sb sj func) /\
  lookup_block incr_lbl func.fn_blocks =
    SOME <|bb_label := incr_lbl; bb_instructions :=
      [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
       mk_inst i2 ASSIGN [Var nv] [idx];
       mk_inst i3 JMP [Label cond_lbl] []]|> /\
  not_local_ptr cenv rest idx /\ not_local_ptr cenv rest nv /\
  p <> idx /\ p <> nv /\
  (!x. saved_base = Var x ==> x <> idx /\ x <> nv) /\
  (!fuel rr. run_from fuel ctx func s2 = rr /\ (!e. rr <> Error e) ==>
    ?fuel'. run_from fuel' ctx func cc = rr) ==>
  ((r = INL () \/ r = INR ContinueException) /\
   ?next. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst cond_lbl st (k+1) (es2 with scopes := rest) next /\
     (!fuel rr. run_from fuel ctx func next = rr /\ (!e. rr <> Error e) ==>
       ?fuel'. run_from fuel' ctx func cc = rr)) \/
  (r = INR BreakException /\
   ?next. next.vs_current_bb = exit_lbl /\ next.vs_inst_idx = 0 /\
     ~next.vs_halted /\
     stmt_state_rel ctx func cenv cx (es2 with scopes := rest) next /\
     (!fuel rr. run_from fuel ctx func next = rr /\ (!e. rr <> Error e) ==>
       ?fuel'. run_from fuel' ctx func cc = rr)) \/
  (?fuel rr. run_from fuel ctx func cc = rr /\ exit_result rr /\
    stmt_exit RetQ (es2 with scopes := rest) r rr)
Proof
  rpt gen_tac >>
  disch_then (strip_assume_tac o MATCH_MP array_for_iteration_frames) >>
  metis_tac[]
QED

Theorem array_for_iteration_framed:
  !ctx func cx RetQ cenv bc m ei stmts r es2 sa sb s2 cenv' sc rest
   idx k p dst saved_base arr_base ainst sz st P vs id sj exit_lbl incr_lbl
   cond_lbl nv i1 i2 i3 cc caller.
  (!x. not_fresh_at caller x ==> not_fresh_at sa x /\ x <> idx /\ x <> nv) /\
  (stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc m (eval_stmts cx stmts) ei /\
   m sa = (cenv',sb) /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
   local_ptrs_reserved bc sa /\ ret_pc_ok bc sa s2 /\
   ~block_is_terminated sa /\ stmt_res_ok (InLoop exit_lbl incr_lbl) r /\
   stmt_state_rel ctx func bc cx ei s2 /\ ~s2.vs_halted /\
   s2.vs_current_bb = sa.cs_current_bb /\
   s2.vs_inst_idx = LENGTH sa.cs_current_insts /\
   cenv_top_ext cenv bc ei.scopes /\ eval_stmts cx stmts ei = (r,es2) /\
   es2.scopes = sc :: rest /\
   (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) /\
   lookup_var idx s2 = SOME (n2w k) /\ eval_operand saved_base s2 = SOME arr_base /\
   lookup_var p s2 = SOME dst /\
   FLOOKUP s2.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
   ret_pc_ok cenv st s2 /\ not_fresh_at sa idx /\ not_fresh_at sa p /\
   (!x. saved_base = Var x ==> not_fresh_at sa x) /\
   (!l. saved_base <> Label l) /\ k < LENGTH vs /\
   (r = INL () \/ r = INR ContinueException ==>
     P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE) /\
   (r = INL () ==>
     sj.cs_blocks = sb.cs_blocks /\ sj.cs_current_bb = sb.cs_current_bb /\
     sj.cs_current_insts = sb.cs_current_insts ++
       [mk_inst sb.cs_next_id JMP [Label incr_lbl] []] /\ fn_has_code sb sj func) /\
   lookup_block incr_lbl func.fn_blocks =
     SOME <|bb_label := incr_lbl; bb_instructions :=
       [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
        mk_inst i2 ASSIGN [Var nv] [idx];
        mk_inst i3 JMP [Label cond_lbl] []]|> /\
   not_local_ptr cenv rest idx /\ not_local_ptr cenv rest nv /\
   p <> idx /\ p <> nv /\
   (!x. saved_base = Var x ==> x <> idx /\ x <> nv) /\
   (!fuel rr. run_from fuel ctx func s2 = rr /\ (!e. rr <> Error e) ==>
     ?fuel'. run_from fuel' ctx func cc = rr)) ==>
  ((r = INL () \/ r = INR ContinueException) /\
   ?next. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst cond_lbl st (k+1) (es2 with scopes := rest) next /\
     (!x w. not_fresh_at caller x /\ lookup_var x s2 = SOME w ==>
       lookup_var x next = SOME w) /\
     (!aid b. FLOOKUP s2.vs_allocas aid = SOME b ==>
       FLOOKUP next.vs_allocas aid = SOME b) /\
     (!fuel rr. run_from fuel ctx func next = rr /\ (!e. rr <> Error e) ==>
       ?fuel'. run_from fuel' ctx func cc = rr)) \/
  (r = INR BreakException /\
   ?next. next.vs_current_bb = exit_lbl /\ next.vs_inst_idx = 0 /\
     ~next.vs_halted /\
     stmt_state_rel ctx func cenv cx (es2 with scopes := rest) next /\
     (!x w. not_fresh_at caller x /\ lookup_var x s2 = SOME w ==>
       lookup_var x next = SOME w) /\
     (!aid b. FLOOKUP s2.vs_allocas aid = SOME b ==>
       FLOOKUP next.vs_allocas aid = SOME b) /\
     (!fuel rr. run_from fuel ctx func next = rr /\ (!e. rr <> Error e) ==>
       ?fuel'. run_from fuel' ctx func cc = rr)) \/
  (?fuel rr. run_from fuel ctx func cc = rr /\ exit_result rr /\
    stmt_exit RetQ (es2 with scopes := rest) r rr)
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  disch_then (strip_assume_tac o MATCH_MP array_for_iteration_frames)
  >- (disj1_tac >> simp[] >> qexists_tac `next` >> simp[] >> metis_tac[])
  >- (disj1_tac >> simp[] >> qexists_tac `next` >> simp[] >> metis_tac[])
  >- (disj2_tac >> disj1_tac >> simp[] >> qexists_tac `next` >> simp[] >> metis_tac[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem array_body_compiler_env:
  compile_stmts bc lctx ty stmts sa = ((),sb) ==>
  ?bc'. stmts_env bc lctx ty stmts sa = (bc',sb)
Proof
  simp[compile_stmts_env] >>
  Cases_on `stmts_env bc lctx ty stmts sa` >> simp[]
QED

Theorem array_condition_exit_framed:
  !ctx func cenv cx P vs id idx saved_base arr_base p dst sz ainst cond_lbl st
   es cc dv j1 j2 exit_lbl stmts_lbl caller.
  lookup_block cond_lbl func.fn_blocks =
    SOME <|bb_label := cond_lbl; bb_instructions :=
      [mk_inst j1 EQ [Var idx; Lit (n2w (LENGTH vs))] [dv];
       mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []]|> /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond_lbl st (LENGTH vs) es cc /\
  LENGTH vs < dimword (:256) /\
  not_local_ptr cenv es.scopes dv /\ dv <> idx /\ dv <> p /\
  (!x. saved_base = Var x ==> x <> dv) /\
  (!x. not_fresh_at caller x ==> x <> dv) ==>
  ?next. next.vs_current_bb = exit_lbl /\ next.vs_inst_idx = 0 /\
    ~next.vs_halted /\ stmt_state_rel ctx func cenv cx es next /\
    (!x w. not_fresh_at caller x /\ lookup_var x cc = SOME w ==>
      lookup_var x next = SOME w) /\
    (!aid b. FLOOKUP cc.vs_allocas aid = SOME b ==>
      FLOOKUP next.vs_allocas aid = SOME b) /\
    (!fuel rr. run_from fuel ctx func next = rr /\ (!e. rr <> Error e) ==>
      ?fuel'. run_from fuel' ctx func cc = rr)
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH vs = LENGTH vs` by simp[] >>
  drule_all array_condition_boundary >> strip_tac >>
  qexists_tac `next` >> fs[array_loop_inv_def] >> metis_tac[]
QED

(* Fully anchored logical input/output contracts for the copy prefix. *)
Definition array_entry_inputs_def:
  array_entry_inputs ctx func cenv bc cx es s id p sz dst ainst tv v et tenv sa sb0
    idx saved_base arr_base k stride ov ep j3 j4 bb st <=>
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocMemory F et et sa = ((),sb0) /\
  stride = type_memory_size tv /\ type_memory_bytes cenv et = stride /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n arr_base + k * stride) s.vs_memory /\
  w2n arr_base + k * stride < dimword (:256) /\ stride + 64 < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\ local_ptrs_reserved bc sa /\
  lookup_scopes id es.scopes = NONE /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes ep /\
  lookup_var idx s = SOME (n2w k) /\ eval_operand saved_base s = SOME arr_base /\
  lookup_var p s = SOME dst /\ p <> ov /\ p <> ep /\
  (!x. saved_base = Var x ==> x <> ov) /\ not_fresh_at sa ep /\
  MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
  ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\ stride <= sz /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  sb0.cs_current_insts =
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [saved_base; Var ov] [ep]] ++ emitted_insts sa sb0 /\
  s.vs_current_bb = sb0.cs_current_bb /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  ret_pc_ok bc st s /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep)
End

Definition array_entry_ready_def:
  array_entry_ready ctx func bc cx es id tv v sb0 sa ov ep st s s2 <=>
  s2.vs_current_bb = sb0.cs_current_bb /\
  s2.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ~s2.vs_halted /\
  stmt_state_rel ctx func bc cx
    (es with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes) s2 /\
  ret_pc_ok bc st s2 /\ s2.vs_allocas = s.vs_allocas /\
  (!x. not_fresh_at sa x /\ x <> ov /\ x <> ep ==>
    lookup_var x s2 = lookup_var x s) /\
  (!fuel. run_from fuel ctx func s = run_from fuel ctx func s2)
End

Theorem array_entry_inputs_run:
  array_entry_inputs ctx func cenv bc cx es s id p sz dst ainst tv v et tenv sa sb0
    idx saved_base arr_base k stride ov ep j3 j4 bb st ==>
  ?s2. array_entry_ready ctx func bc cx es id tv v sb0 sa ov ep st s s2
Proof
  pure_rewrite_tac[array_entry_inputs_def, array_entry_ready_def] >>
  MATCH_ACCEPT_TAC array_for_body_entry
QED

Theorem array_for_code_entry_inputs:
  array_for_code func cenv bc ty stmts id et tv (LENGTH vs) stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst stmts_lbl st k es s /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv (EL k vs) /\
  val_wf tv (EL k vs) /\
  val_in_memory tv (EL k vs) (w2n arr_base + k * stride) s.vs_memory /\
  w2n arr_base + k * stride < dimword (:256) /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\ ret_pc_ok bc sb0 s /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) ==>
  array_entry_inputs ctx func cenv bc cx es s id p sz dst ainst tv (EL k vs)
    et tenv sa sb0 idx saved_base arr_base k stride ov ep j3 j4 bb sb0
Proof
  pure_rewrite_tac[array_for_code_def, array_loop_inv_def, array_entry_inputs_def] >>
  strip_tac >> asm_rewrite_tac[] >>
  fs[ALL_DISTINCT] >> metis_tac[]
QED

Theorem array_entry_ready_runtime:
  array_entry_ready ctx func bc cx es id tv v sb0 sa ov ep sb0 s s2 /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst lbl st k es s /\
  not_fresh_at sa idx /\ idx <> ov /\ idx <> ep /\
  not_fresh_at sa p /\ p <> ov /\ p <> ep /\
  (!x. saved_base = Var x ==> not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
  (!l. saved_base <> Label l) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) ==>
  lookup_var idx s2 = SOME (n2w k) /\
  eval_operand saved_base s2 = SOME arr_base /\ lookup_var p s2 = SOME dst /\
  FLOOKUP s2.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
  ret_pc_ok cenv st s2
Proof
  strip_tac >>
  `ret_pc_ok cenv st s2` by
    (irule array_ret_pc_copy_frame >>
     fs[array_entry_ready_def, array_loop_inv_def] >> metis_tac[]) >>
  fs[array_entry_ready_def, array_loop_inv_def] >>
  irule array_saved_operand_frame >> metis_tac[]
QED

Theorem array_for_code_iteration_static:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj ==>
  fn_has_code sb0 sb1 func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved bc sb0 /\ ~block_is_terminated sb0 /\
  lookup_block incr_lbl func.fn_blocks =
    SOME <|bb_label := incr_lbl; bb_instructions :=
      [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
       mk_inst i2 ASSIGN [Var nv] [idx];
       mk_inst i3 JMP [Label cond_lbl] []]|> /\
  (!scs. not_local_ptr cenv scs idx /\ not_local_ptr cenv scs nv) /\
  p <> idx /\ p <> nv /\
  (!x. saved_base = Var x ==> x <> idx /\ x <> nv) /\
  not_fresh_at sa idx /\ idx <> ov /\ idx <> ep /\
  not_fresh_at sa p /\ p <> ov /\ p <> ep /\
  (!x. saved_base = Var x ==> not_fresh_at sa x /\ x <> ov /\ x <> ep)
Proof
  simp[array_for_code_def, ALL_DISTINCT] >> metis_tac[]
QED

Theorem array_for_code_entry_static:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj ==>
  (!scs. not_local_ptr cenv scs dv) /\ dv <> idx /\ dv <> p /\
  (!x. saved_base = Var x ==> x <> dv)
Proof
  simp[array_for_code_def, ALL_DISTINCT] >> metis_tac[]
QED

Theorem array_for_step_framed:
  !ctx func cenv bc ty stmts id et tv vs stride saved_base p sz ainst idx
   dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl j1 j2 j3 j4 i1 i2 i3
   sa sb0 sb1 sj cx P arr_base dst st k es cc tenv bb RetQ ei r es2 sc rest caller.
  array_for_code func cenv bc ty stmts id et tv (LENGTH vs) stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond_lbl st k es cc /\ k < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv (EL k vs) /\
  val_wf tv (EL k vs) /\ w2n arr_base + k * stride < dimword (:256) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  (!s. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst stmts_lbl st k es s ==>
     val_in_memory tv (EL k vs) (w2n arr_base + k * stride) s.vs_memory /\
     ret_pc_ok bc sb0 s) /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
  (!x. not_fresh_at caller x ==>
    not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> ep) /\
  (!x. not_fresh_at caller x ==>
    not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
  not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
  (!x. saved_base = Var x ==> not_fresh_at sb0 x) /\
  (!l. saved_base <> Label l) /\
  ei = es with scopes := (FEMPTY |+ (id,
    <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes /\
  cenv_top_ext cenv bc ei.scopes /\
  stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
    (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts) ei /\
  eval_stmts cx stmts ei = (r,es2) /\ stmt_res_ok (InLoop exit_lbl incr_lbl) r /\
  es2.scopes = sc :: rest /\
  (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) /\
  (r = INL () \/ r = INR ContinueException ==>
    P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE) /\
  (r = INL () ==>
    sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
    sj.cs_current_insts = sb1.cs_current_insts ++
      [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\ fn_has_code sb1 sj func) ==>
  ((r = INL () \/ r = INR ContinueException) /\
   ?next. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst cond_lbl st (k+1) (es2 with scopes := rest) next /\
     (!x w. not_fresh_at caller x /\ lookup_var x cc = SOME w ==>
       lookup_var x next = SOME w) /\
     (!aid b. FLOOKUP cc.vs_allocas aid = SOME b ==>
       FLOOKUP next.vs_allocas aid = SOME b) /\
     (!fuel rr. run_from fuel ctx func next = rr /\ (!e. rr <> Error e) ==>
       ?fuel'. run_from fuel' ctx func cc = rr)) \/
  (r = INR BreakException /\
   ?next. next.vs_current_bb = exit_lbl /\ next.vs_inst_idx = 0 /\ ~next.vs_halted /\
     stmt_state_rel ctx func cenv cx (es2 with scopes := rest) next /\
     (!x w. not_fresh_at caller x /\ lookup_var x cc = SOME w ==>
       lookup_var x next = SOME w) /\
     (!aid b. FLOOKUP cc.vs_allocas aid = SOME b ==>
       FLOOKUP next.vs_allocas aid = SOME b) /\
     (!fuel rr. run_from fuel ctx func next = rr /\ (!e. rr <> Error e) ==>
       ?fuel'. run_from fuel' ctx func cc = rr)) \/
  (?fuel rr. run_from fuel ctx func cc = rr /\ exit_result rr /\
    stmt_exit RetQ (es2 with scopes := rest) r rr)
Proof
  rpt gen_tac >> strip_tac >>
  drule array_for_code_condition >> strip_tac >>
  drule array_for_code_entry_static >> strip_tac >>
  `LENGTH vs = LENGTH vs` by simp[] >>
  `not_local_ptr cenv es.scopes dv` by metis_tac[] >>
  drule_all array_condition_boundary >> strip_tac >>
  rename1 `array_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s` >>
  `k <> LENGTH vs` by decide_tac >> gvs[] >>
  `cenv_top_ext cenv bc (FEMPTY :: es.scopes)` by
    (irule array_for_code_scope_frame >>
     fs[array_loop_inv_def] >> metis_tac[]) >>
  first_x_assum drule >> strip_tac >>
  drule_all array_for_code_entry_inputs >>
  disch_then (strip_assume_tac o MATCH_MP array_entry_inputs_run) >>
  rename1 `array_entry_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ s2` >>
  drule array_for_code_iteration_static >> strip_tac >>
  drule_all array_entry_ready_runtime >> strip_tac >>
  `!x w. not_fresh_at caller x /\ lookup_var x cc = SOME w ==>
     lookup_var x s2 = SOME w` by
    (fs[array_entry_ready_def] >> metis_tac[]) >>
  `!aid b. FLOOKUP cc.vs_allocas aid = SOME b ==>
     FLOOKUP s2.vs_allocas aid = SOME b` by
    (fs[array_entry_ready_def] >> metis_tac[]) >>
  `!fuel rr. run_from fuel ctx func s2 = rr /\ (!e. rr <> Error e) ==>
     ?fuel'. run_from fuel' ctx func cc = rr` by
    (fs[array_entry_ready_def] >> metis_tac[]) >>
  drule array_for_code_stmts >> strip_tac >>
  drule array_body_compiler_env >> strip_tac >>
  qhdtm_x_assum `array_for_code` kall_tac >>
  qpat_x_assum `array_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cc` kall_tac >>
  qpat_x_assum `array_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s` kall_tac >>
  qhdtm_x_assum `array_entry_ready` mp_tac >>
  pure_rewrite_tac[array_entry_ready_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `stmt_frag _ _ _ _ _ _ _ ei _ _` >>
  `not_local_ptr cenv rest idx /\ not_local_ptr cenv rest nv` by metis_tac[] >>
  `cenv_top_ext cenv bc ei.scopes` by simp[Abbr `ei`] >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`LENGTH vs < _`, `w2n arr_base + _ < _`, `not_local_ptr bc _ _`,
     `lookup_block cond_lbl _ = _`, `lookup_block sb0.cs_current_bb _ = _`,
     `isPREFIX _ _`, `!scs. not_local_ptr _ _ dv`, `dv <> idx`, `dv <> p`,
     `saved_base <> Var dv`, `!x. x <> dv ==> _`, `s.vs_allocas = _`,
     `!fuel. (!e. run_from fuel ctx func s <> Error e) ==> _`,
     `cenv_top_ext _ _ (FEMPTY :: _)`, `ret_pc_ok bc sb0 s`,
     `compile_stmts _ _ _ _ _ = _`, `!scs. not_local_ptr _ _ idx /\ _`,
     `not_fresh_at sa idx`, `idx <> ov`, `idx <> ep`,
     `not_fresh_at sa p`, `p <> ov`, `p <> ep`,
     `!x. saved_base = Var x ==> not_fresh_at sa x /\ _`,
     `s2.vs_allocas = _`, `!x. not_fresh_at sa x /\ _ ==> _`,
     `!fuel. run_from fuel ctx func s = _`,
     `!x z. bc.ce_return_pc = _ ==> _`, `!x z. cenv.ce_return_pc = _ ==> _`,
     `!x. not_fresh_at caller x ==> not_fresh_at sa x /\ _`] >>
  map_every (fn q => qhdtm_x_assum q kall_tac)
    [`evaluate_type`, `value_has_type`, `val_wf`, `val_in_memory`] >>
  drule_all array_for_iteration_framed >> strip_tac
  >- suspend "continue"
  >- suspend "continue"
  >- suspend "break" >>
  suspend "terminal"
QED

Resume array_for_step_framed[continue]:
  markerLib.RESUME_TAC >>
  (rename1 `array_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ next` >>
   disj1_tac >> conj_tac >- simp[] >>
   qexists_tac `next` >> simp[] >> metis_tac[])
QED
Resume array_for_step_framed[break]:
  rename1 `next.vs_current_bb = exit_lbl` >>
  disj2_tac >> disj1_tac >> simp[] >>
  qexists_tac `next` >> simp[] >> metis_tac[]
QED
Resume array_for_step_framed[terminal]:
  disj2_tac >> disj2_tac >> metis_tac[]
QED
Finalise array_for_step_framed

(* Logical composition interfaces: no compiler or interpreter is hidden here. *)
Definition array_run_frame_def:
  array_run_frame ctx func caller s t <=>
  (!x w. not_fresh_at caller x /\ lookup_var x s = SOME w ==>
    lookup_var x t = SOME w) /\
  (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
    FLOOKUP t.vs_allocas aid = SOME b) /\
  (!fuel rr. run_from fuel ctx func t = rr /\ (!e. rr <> Error e) ==>
    ?fuel'. run_from fuel' ctx func s = rr)
End

Definition array_loop_landing_def:
  array_loop_landing ctx func cenv cx caller lbl es s t <=>
  t.vs_current_bb = lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
  stmt_state_rel ctx func cenv cx es t /\ array_run_frame ctx func caller s t
End

Definition array_step_contract_def:
  array_step_contract ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond_lbl exit_lbl st tv stmts RetQ caller <=>
  !k es cc r es2 sc rest.
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond_lbl st k es cc /\ k < LENGTH vs /\
  eval_stmts cx stmts
    (es with scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes) = (r,es2) /\
  es2.scopes = sc :: rest /\
  (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) ==>
  ((r = INL () \/ r = INR ContinueException) /\
   ?next. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst cond_lbl st (k+1) (es2 with scopes := rest) next /\
     array_run_frame ctx func caller cc next) \/
  (r = INR BreakException /\
   ?next. array_loop_landing ctx func cenv cx caller exit_lbl
     (es2 with scopes := rest) cc next) \/
  (?fuel rr. run_from fuel ctx func cc = rr /\ exit_result rr /\
    stmt_exit RetQ (es2 with scopes := rest) r rr)
End

Theorem array_run_frame_trans:
  array_run_frame ctx func caller s t /\ array_run_frame ctx func caller t u ==>
  array_run_frame ctx func caller s u
Proof
  rw[array_run_frame_def] >> metis_tac[]
QED

Theorem array_loop_landing_pullback:
  array_run_frame ctx func caller s t /\
  array_loop_landing ctx func cenv cx caller lbl es t u ==>
  array_loop_landing ctx func cenv cx caller lbl es s u
Proof
  simp[array_loop_landing_def] >> metis_tac[array_run_frame_trans]
QED

Theorem array_drop_head[local]:
  !vs k. k < LENGTH vs ==> DROP k vs = EL k vs :: DROP (k+1) vs
Proof
  Induct >> simp[] >> gen_tac >> Cases_on `k` >> simp[arithmeticTheory.ADD1]
QED

Theorem array_for_loop:
  !m k es cc res es'.
  k + m = LENGTH vs /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond_lbl st k es cc /\
  eval_for cx tv id stmts (DROP k vs) es = (res,es') /\ stmt_res_ok lctx res /\
  array_step_contract ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond_lbl exit_lbl st tv stmts RetQ caller /\
  (!es cc. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst cond_lbl st (LENGTH vs) es cc ==>
     ?next. array_loop_landing ctx func cenv cx caller exit_lbl es cc next) ==>
  (res = INL () /\
   ?next. array_loop_landing ctx func cenv cx caller exit_lbl es' cc next) \/
  (?fuel rr. run_from fuel ctx func cc = rr /\ exit_result rr /\
    stmt_exit RetQ es' res rr)
Proof
  Induct_on `m`
  >- (rpt strip_tac >> gvs[] >>
      gvs[DROP_LENGTH_NIL, Once evaluate_def, return_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `k < LENGTH vs` by decide_tac >>
  `lookup_scopes id es.scopes = NONE` by fs[array_loop_inv_def] >>
  `DROP k vs = EL k vs :: DROP (k+1) vs` by metis_tac[array_drop_head] >>
  qpat_x_assum `eval_for _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_all eval_for_cons_cases >> strip_tac
  >- suspend "continue"
  >- suspend "continue"
  >- suspend "break" >> suspend "terminal"
QED

Resume array_for_loop[continue]:
  markerLib.RESUME_TAC >>
  (rename1 `eval_stmts _ _ _ = (r2,es2)` >>
   qhdtm_assum `array_step_contract`
     (fn th => drule_all (REWRITE_RULE [array_step_contract_def] th)) >>
   strip_tac >> gvs[stmt_exit_loop_ctl] >>
   rename1 `array_run_frame _ _ _ cc next` >>
   `(k+1) + m = LENGTH vs` by decide_tac >>
   qpat_x_assum `!k es cc res es'. _` (fn th => drule_all th) >>
   strip_tac
   >- (drule_all array_loop_landing_pullback >> strip_tac >>
       disj1_tac >> metis_tac[]) >>
   disj2_tac >> fs[array_run_frame_def] >> metis_tac[exit_result_not_error])
QED
Resume array_for_loop[break]:
  qhdtm_assum `array_step_contract`
    (fn th => drule_all (REWRITE_RULE [array_step_contract_def] th)) >>
  strip_tac >> gvs[stmt_exit_loop_ctl] >> metis_tac[]
QED
Resume array_for_loop[terminal]:
  qhdtm_assum `array_step_contract`
    (fn th => drule_all (REWRITE_RULE [array_step_contract_def] th)) >>
  strip_tac >> gvs[] >> metis_tac[]
QED
Finalise array_for_loop

(* Backedges are needed only after an ordinary reachable body landing. *)
Theorem array_for_iteration_frames_open[local]:
  !ctx func cx RetQ cenv bc m ei stmts r es2 sa sb s2 cenv' sc rest
   idx k p dst saved_base arr_base ainst sz st P vs id sj exit_lbl incr_lbl
   cond_lbl nv i1 i2 i3 cc.
  stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc m (eval_stmts cx stmts) ei /\
  m sa = (cenv',sb) /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved bc sa /\ ret_pc_ok bc sa s2 /\
  ~block_is_terminated sa /\ stmt_res_ok (InLoop exit_lbl incr_lbl) r /\
  stmt_state_rel ctx func bc cx ei s2 /\ ~s2.vs_halted /\
  s2.vs_current_bb = sa.cs_current_bb /\
  s2.vs_inst_idx = LENGTH sa.cs_current_insts /\
  cenv_top_ext cenv bc ei.scopes /\ eval_stmts cx stmts ei = (r,es2) /\
  es2.scopes = sc :: rest /\
  (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) /\
  lookup_var idx s2 = SOME (n2w k) /\ eval_operand saved_base s2 = SOME arr_base /\
  lookup_var p s2 = SOME dst /\
  FLOOKUP s2.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
  ret_pc_ok cenv st s2 /\ not_fresh_at sa idx /\ not_fresh_at sa p /\
  (!x. saved_base = Var x ==> not_fresh_at sa x) /\
  (!l. saved_base <> Label l) /\ k < LENGTH vs /\
  (r = INL () \/ r = INR ContinueException ==>
    P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE) /\
  (~block_is_terminated sb ==>
    sj.cs_blocks = sb.cs_blocks /\ sj.cs_current_bb = sb.cs_current_bb /\
    sj.cs_current_insts = sb.cs_current_insts ++
      [mk_inst sb.cs_next_id JMP [Label incr_lbl] []] /\ fn_has_code sb sj func) /\
  lookup_block incr_lbl func.fn_blocks =
    SOME <|bb_label := incr_lbl; bb_instructions :=
      [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
       mk_inst i2 ASSIGN [Var nv] [idx];
       mk_inst i3 JMP [Label cond_lbl] []]|> /\
  not_local_ptr cenv rest idx /\ not_local_ptr cenv rest nv /\
  p <> idx /\ p <> nv /\
  (!x. saved_base = Var x ==> x <> idx /\ x <> nv) /\
  (!fuel rr. run_from fuel ctx func s2 = rr /\ (!e. rr <> Error e) ==>
    ?fuel'. run_from fuel' ctx func cc = rr) ==>
  ((r = INL () \/ r = INR ContinueException) /\
   ?next. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst cond_lbl st (k+1) (es2 with scopes := rest) next /\
     (!x w. not_fresh_at sa x /\ x <> idx /\ x <> nv /\
       lookup_var x s2 = SOME w ==> lookup_var x next = SOME w) /\
     (!aid b. FLOOKUP s2.vs_allocas aid = SOME b ==>
       FLOOKUP next.vs_allocas aid = SOME b) /\
     (!fuel rr. run_from fuel ctx func next = rr /\ (!e. rr <> Error e) ==>
       ?fuel'. run_from fuel' ctx func cc = rr)) \/
  (r = INR BreakException /\
   ?next. next.vs_current_bb = exit_lbl /\ next.vs_inst_idx = 0 /\
     ~next.vs_halted /\
     stmt_state_rel ctx func cenv cx (es2 with scopes := rest) next /\
     (!x w. not_fresh_at sa x /\ x <> idx /\ x <> nv /\
       lookup_var x s2 = SOME w ==> lookup_var x next = SOME w) /\
     (!aid b. FLOOKUP s2.vs_allocas aid = SOME b ==>
       FLOOKUP next.vs_allocas aid = SOME b) /\
     (!fuel rr. run_from fuel ctx func next = rr /\ (!e. rr <> Error e) ==>
       ?fuel'. run_from fuel' ctx func cc = rr)) \/
  (?fuel rr. run_from fuel ctx func cc = rr /\ exit_result rr /\
    stmt_exit RetQ (es2 with scopes := rest) r rr)
Proof
  rpt gen_tac >> strip_tac >> drule_all array_body_fragment_run >> strip_tac
  >- (`!fuel rr. run_from fuel ctx func s = rr /\ (!e. rr <> Error e) ==>
         ?fuel'. run_from fuel' ctx func cc = rr` by metis_tac[] >>
      Cases_on `r = INR BreakException`
      >- (disj2_tac >> disj1_tac >> simp[] >> qexists_tac `s` >>
          fs[stmt_lands_def] >> metis_tac[]) >>
      `r = INL () \/ r = INR ContinueException` by fs[stmt_lands_def] >>
      drule_all array_body_runtime_frame >> strip_tac >>
      `array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
         ainst s.vs_current_bb st k (es2 with scopes := rest)
         (s with vs_inst_idx := 0)` by
        (simp[array_loop_inv_def, stmt_state_rel_inst_idx, lookup_var_def,
              ret_pc_ok_def] >>
         Cases_on `saved_base` >> gvs[eval_operand_def, lookup_var_def, ret_pc_ok_def]) >>
      `?next. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
         ainst cond_lbl st (k+1) (es2 with scopes := rest) next /\
         (!x. x <> idx /\ x <> nv ==> lookup_var x next = lookup_var x s) /\
         next.vs_allocas = s.vs_allocas /\
         (!fuel rr. run_from fuel ctx func next = rr /\ (!e. rr <> Error e) ==>
           ?fuel'. run_from fuel' ctx func cc = rr)` by
        (irule array_body_continue_iteration_framed >> simp[] >>
         (conj_tac >- metis_tac[]) >>
         goal_assum (drule_at (Pat `lookup_block _ _ = _`)) >>
         goal_assum (drule_at (Pat `stmt_lands _ _ _ _`)) >>
         qexists_tac `sj` >> metis_tac[]) >>
      disj1_tac >> simp[] >> qexists_tac `next` >> simp[] >> metis_tac[]) >>
  disj2_tac >> disj2_tac >> drule_all array_body_exit_pullback >> metis_tac[]
QED

Theorem array_for_iteration_framed_open:
  !ctx func cx RetQ cenv bc m ei stmts r es2 sa sb s2 cenv' sc rest
   idx k p dst saved_base arr_base ainst sz st P vs id sj exit_lbl incr_lbl
   cond_lbl nv i1 i2 i3 cc caller.
  (!x. not_fresh_at caller x ==> not_fresh_at sa x /\ x <> idx /\ x <> nv) /\
  (stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc m (eval_stmts cx stmts) ei /\
   m sa = (cenv',sb) /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
   local_ptrs_reserved bc sa /\ ret_pc_ok bc sa s2 /\
   ~block_is_terminated sa /\ stmt_res_ok (InLoop exit_lbl incr_lbl) r /\
   stmt_state_rel ctx func bc cx ei s2 /\ ~s2.vs_halted /\
   s2.vs_current_bb = sa.cs_current_bb /\
   s2.vs_inst_idx = LENGTH sa.cs_current_insts /\
   cenv_top_ext cenv bc ei.scopes /\ eval_stmts cx stmts ei = (r,es2) /\
   es2.scopes = sc :: rest /\
   (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) /\
   lookup_var idx s2 = SOME (n2w k) /\ eval_operand saved_base s2 = SOME arr_base /\
   lookup_var p s2 = SOME dst /\
   FLOOKUP s2.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
   ret_pc_ok cenv st s2 /\ not_fresh_at sa idx /\ not_fresh_at sa p /\
   (!x. saved_base = Var x ==> not_fresh_at sa x) /\
   (!l. saved_base <> Label l) /\ k < LENGTH vs /\
   (r = INL () \/ r = INR ContinueException ==>
     P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE) /\
   (~block_is_terminated sb ==>
     sj.cs_blocks = sb.cs_blocks /\ sj.cs_current_bb = sb.cs_current_bb /\
     sj.cs_current_insts = sb.cs_current_insts ++
       [mk_inst sb.cs_next_id JMP [Label incr_lbl] []] /\ fn_has_code sb sj func) /\
   lookup_block incr_lbl func.fn_blocks =
     SOME <|bb_label := incr_lbl; bb_instructions :=
       [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
        mk_inst i2 ASSIGN [Var nv] [idx];
        mk_inst i3 JMP [Label cond_lbl] []]|> /\
   not_local_ptr cenv rest idx /\ not_local_ptr cenv rest nv /\
   p <> idx /\ p <> nv /\
   (!x. saved_base = Var x ==> x <> idx /\ x <> nv) /\
   (!fuel rr. run_from fuel ctx func s2 = rr /\ (!e. rr <> Error e) ==>
     ?fuel'. run_from fuel' ctx func cc = rr)) ==>
  ((r = INL () \/ r = INR ContinueException) /\
   ?next. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst cond_lbl st (k+1) (es2 with scopes := rest) next /\
     (!x w. not_fresh_at caller x /\ lookup_var x s2 = SOME w ==>
       lookup_var x next = SOME w) /\
     (!aid b. FLOOKUP s2.vs_allocas aid = SOME b ==>
       FLOOKUP next.vs_allocas aid = SOME b) /\
     (!fuel rr. run_from fuel ctx func next = rr /\ (!e. rr <> Error e) ==>
       ?fuel'. run_from fuel' ctx func cc = rr)) \/
  (r = INR BreakException /\
   ?next. next.vs_current_bb = exit_lbl /\ next.vs_inst_idx = 0 /\
     ~next.vs_halted /\
     stmt_state_rel ctx func cenv cx (es2 with scopes := rest) next /\
     (!x w. not_fresh_at caller x /\ lookup_var x s2 = SOME w ==>
       lookup_var x next = SOME w) /\
     (!aid b. FLOOKUP s2.vs_allocas aid = SOME b ==>
       FLOOKUP next.vs_allocas aid = SOME b) /\
     (!fuel rr. run_from fuel ctx func next = rr /\ (!e. rr <> Error e) ==>
       ?fuel'. run_from fuel' ctx func cc = rr)) \/
  (?fuel rr. run_from fuel ctx func cc = rr /\ exit_result rr /\
    stmt_exit RetQ (es2 with scopes := rest) r rr)
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  disch_then (strip_assume_tac o MATCH_MP array_for_iteration_frames_open)
  >- (disj1_tac >> simp[] >> qexists_tac `next` >> simp[] >> metis_tac[])
  >- (disj1_tac >> simp[] >> qexists_tac `next` >> simp[] >> metis_tac[])
  >- (disj2_tac >> disj1_tac >> simp[] >> qexists_tac `next` >> simp[] >> metis_tac[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem array_for_step_framed_open:
  !ctx func cenv bc ty stmts id et tv vs stride saved_base p sz ainst idx
   dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl j1 j2 j3 j4 i1 i2 i3
   sa sb0 sb1 sj cx P arr_base dst st k es cc tenv bb RetQ ei r es2 sc rest caller.
  array_for_code func cenv bc ty stmts id et tv (LENGTH vs) stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond_lbl st k es cc /\ k < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv (EL k vs) /\
  val_wf tv (EL k vs) /\ w2n arr_base + k * stride < dimword (:256) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  (!s. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst stmts_lbl st k es s ==>
     val_in_memory tv (EL k vs) (w2n arr_base + k * stride) s.vs_memory /\
     ret_pc_ok bc sb0 s) /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
  (!x. not_fresh_at caller x ==>
    not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> ep) /\
  (!x. not_fresh_at caller x ==>
    not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
  not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
  (!x. saved_base = Var x ==> not_fresh_at sb0 x) /\
  (!l. saved_base <> Label l) /\
  ei = es with scopes := (FEMPTY |+ (id,
    <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes /\
  cenv_top_ext cenv bc ei.scopes /\
  stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
    (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts) ei /\
  eval_stmts cx stmts ei = (r,es2) /\ stmt_res_ok (InLoop exit_lbl incr_lbl) r /\
  es2.scopes = sc :: rest /\
  (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) /\
  (r = INL () \/ r = INR ContinueException ==>
    P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE) ==>
  ((r = INL () \/ r = INR ContinueException) /\
   ?next. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst cond_lbl st (k+1) (es2 with scopes := rest) next /\
     (!x w. not_fresh_at caller x /\ lookup_var x cc = SOME w ==>
       lookup_var x next = SOME w) /\
     (!aid b. FLOOKUP cc.vs_allocas aid = SOME b ==>
       FLOOKUP next.vs_allocas aid = SOME b) /\
     (!fuel rr. run_from fuel ctx func next = rr /\ (!e. rr <> Error e) ==>
       ?fuel'. run_from fuel' ctx func cc = rr)) \/
  (r = INR BreakException /\
   ?next. next.vs_current_bb = exit_lbl /\ next.vs_inst_idx = 0 /\ ~next.vs_halted /\
     stmt_state_rel ctx func cenv cx (es2 with scopes := rest) next /\
     (!x w. not_fresh_at caller x /\ lookup_var x cc = SOME w ==>
       lookup_var x next = SOME w) /\
     (!aid b. FLOOKUP cc.vs_allocas aid = SOME b ==>
       FLOOKUP next.vs_allocas aid = SOME b) /\
     (!fuel rr. run_from fuel ctx func next = rr /\ (!e. rr <> Error e) ==>
       ?fuel'. run_from fuel' ctx func cc = rr)) \/
  (?fuel rr. run_from fuel ctx func cc = rr /\ exit_result rr /\
    stmt_exit RetQ (es2 with scopes := rest) r rr)
Proof
  rpt gen_tac >> strip_tac >>
  drule array_for_code_condition >> strip_tac >>
  drule array_for_code_entry_static >> strip_tac >>
  `LENGTH vs = LENGTH vs` by simp[] >>
  `not_local_ptr cenv es.scopes dv` by metis_tac[] >>
  drule_all array_condition_boundary >> strip_tac >>
  rename1 `array_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s` >>
  `k <> LENGTH vs` by decide_tac >> gvs[] >>
  `cenv_top_ext cenv bc (FEMPTY :: es.scopes)` by
    (irule array_for_code_scope_frame >>
     fs[array_loop_inv_def] >> metis_tac[]) >>
  first_x_assum drule >> strip_tac >>
  drule_all array_for_code_entry_inputs >>
  disch_then (strip_assume_tac o MATCH_MP array_entry_inputs_run) >>
  rename1 `array_entry_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ s2` >>
  drule array_for_code_iteration_static >> strip_tac >>
  drule_all array_entry_ready_runtime >> strip_tac >>
  `!x w. not_fresh_at caller x /\ lookup_var x cc = SOME w ==>
     lookup_var x s2 = SOME w` by (fs[array_entry_ready_def] >> metis_tac[]) >>
  `!aid b. FLOOKUP cc.vs_allocas aid = SOME b ==>
     FLOOKUP s2.vs_allocas aid = SOME b` by (fs[array_entry_ready_def] >> metis_tac[]) >>
  drule array_for_code_stmts >> strip_tac >>
  drule array_body_compiler_env >> strip_tac >>
  `~block_is_terminated sb1 ==>
     sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
     sj.cs_current_insts = sb1.cs_current_insts ++
       [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\ fn_has_code sb1 sj func` by
    fs[array_for_code_def] >>
  qhdtm_x_assum `array_for_code` kall_tac >>
  qhdtm_x_assum `array_entry_ready` mp_tac >>
  pure_rewrite_tac[array_entry_ready_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `stmt_frag _ _ _ _ _ _ _ ei _ _` >>
  `cenv_top_ext cenv bc ei.scopes` by simp[Abbr `ei`] >>
  `!fuel rr. run_from fuel ctx func s2 = rr /\ (!e. rr <> Error e) ==>
     ?fuel'. run_from fuel' ctx func cc = rr` by metis_tac[] >>
  `not_local_ptr cenv rest idx /\ not_local_ptr cenv rest nv` by metis_tac[] >>
  map_every (fn q => qhdtm_x_assum q kall_tac)
    [`array_loop_inv`, `array_loop_inv`, `evaluate_type`, `value_has_type`,
     `val_wf`, `val_in_memory`, `compile_stmts`] >>
  drule_all array_for_iteration_framed_open >> strip_tac
  >- suspend "continue"
  >- suspend "continue"
  >- suspend "break" >>
  suspend "terminal"
QED
Resume array_for_step_framed_open[continue]:
  markerLib.RESUME_TAC >>
  (rename1 `array_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ next` >>
   disj1_tac >> conj_tac >- simp[] >>
   qexists_tac `next` >> simp[] >> metis_tac[])
QED
Resume array_for_step_framed_open[break]:
  rename1 `next.vs_current_bb = exit_lbl` >>
  disj2_tac >> disj1_tac >> simp[] >>
  qexists_tac `next` >> simp[] >> metis_tac[]
QED
Resume array_for_step_framed_open[terminal]:
  disj2_tac >> disj2_tac >> metis_tac[]
QED
Finalise array_for_step_framed_open
