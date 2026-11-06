(*
 * Loop simulation for `for x in arr` where `arr` is a local DynArray.
 *
 * The compiled loop differs from the fixed-array one in two places: the
 * condition block compares the index with a length register `lv` (loaded
 * once before the loop) instead of a literal, and the element address is
 * `arr + (32 + idx * stride)`, a three-instruction prefix skipping the
 * length word.  Everything else (increment block, element copy, body,
 * cleanup, gas) reuses stmtSimForArrayLoop's lemmas unchanged; the loop
 * invariant is still array_loop_inv, with the length register kept by the
 * caller frame.
 *
 * TOP-LEVEL:
 *   dynarray_for_loop_counted - the whole loop from the condition block
 *)
Theory whitelistForIterDynLoop
Ancestors
  loweringPosts stmtSimDefs stmtSimProps
  stmtSimForArrayParts stmtSimForArray stmtSimForArrayLoop stmtLowering compileEnv
  fragExec loweringSlice localPtrsProps exprLoweringProps emitHelper
  venomInst venomState venomExecSemantics vyperState valueEncoding
  list rich_list finite_map words integer_word venomExecProofs emitHelperProps
  vyperEvalPreservesScopes stmtSimForParts vyperInterpreter
  fragGasSeq fragGasMode fragGasPath gasCount context gasSummary gasExemptCert
  gasContext gasOutcome gasSummaryCompose stmtSimForRounds

(* The emitted loop, from the condition block on.  As array_for_code, with
   the length register lv as the bound and the 32-byte length word skipped
   in the element address. *)
Definition dynarray_for_code_def:
  dynarray_for_code func cenv bc ty stmts id et tv stride saved_base
    p sz ainst idx dv ov tot ep nv lv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj <=>
    lookup_block cond_lbl func.fn_blocks =
      SOME <| bb_label := cond_lbl;
              bb_instructions :=
                [mk_inst j1 EQ [Var idx; Var lv] [dv];
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
       mk_inst j4 ADD [Lit 32w; Var ov] [tot];
       mk_inst j5 ADD [saved_base; Var tot] [ep]] /\
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
           not_local_ptr cenv scs ov /\ not_local_ptr cenv scs tot /\
           not_local_ptr cenv scs ep /\ not_local_ptr cenv scs nv) /\
    ALL_DISTINCT [idx; dv; ov; tot; ep; nv; p; lv] /\
    (!x. saved_base = Var x ==> ~MEM x [idx; dv; ov; tot; ep; nv]) /\
    not_fresh_at sa idx /\ not_fresh_at sa p /\ not_fresh_at sa ep /\
    (!x. saved_base = Var x ==> not_fresh_at sa x) /\
    stride = type_memory_bytes cenv et /\ stride = type_memory_size tv /\
    stride <= sz /\ stride + 64 < dimword (:256)
End

Theorem dynarray_for_code_scope_frame:
  dynarray_for_code func cenv bc ty stmts id et tv stride saved_base
    p sz ainst idx dv ov tot ep nv lv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj /\
  lookup_scopes id scopes = NONE ==>
  cenv_top_ext cenv bc (FEMPTY :: scopes)
Proof
  simp[dynarray_for_code_def, cenv_top_ext_def] >> rpt strip_tac >>
  rename1 `FLOOKUP bc.ce_vars name <> FLOOKUP cenv.ce_vars name` >>
  `name = id` by
    (spose_not_then assume_tac >>
     qpat_x_assum `!name. name <> id ==> _`
       (qspec_then `name` mp_tac) >> simp[]) >>
  gvs[lookup_scopes_def] >> metis_tac[]
QED

(* The condition block with any right-hand operand. *)
Theorem eq_condition_block:
  !ctx func cc idx rhs dv a b lbl exit_lbl stmts_lbl j1 j2.
    lookup_block lbl func.fn_blocks =
      SOME <| bb_label := lbl;
              bb_instructions :=
                [mk_inst j1 EQ [Var idx; rhs] [dv];
                 mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []] |> /\
    cc.vs_current_bb = lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    lookup_var idx cc = SOME a /\ eval_operand rhs cc = SOME b ==>
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
     qexistsl_tac [`bb`, `mk_inst j1 EQ [Var idx; rhs] [dv]`] >>
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
     gvs[step_inst_base_opcode_eqs, bool_to_word_def, eval_operand_def,
          lookup_var_def, FLOOKUP_UPDATE, jump_to_def, update_var_def]) >>
  fs[]
QED

Theorem dynarray_condition_boundary:
  !ctx func cenv cx P vs id idx saved_base base p dst sz ainst cond_lbl st
   k es cc lv dv j1 j2 exit_lbl stmts_lbl.
  lookup_block cond_lbl func.fn_blocks =
    SOME <| bb_label := cond_lbl;
            bb_instructions :=
              [mk_inst j1 EQ [Var idx; Var lv] [dv];
               mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []] |> /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base base p dst sz
    ainst cond_lbl st k es cc /\
  lookup_var lv cc = SOME (n2w (LENGTH vs)) /\ LENGTH vs < dimword (:256) /\
  not_local_ptr cenv es.scopes dv /\ dv <> idx /\ dv <> p /\
  (!x. saved_base = Var x ==> x <> dv) ==>
  ?next.
    array_loop_inv ctx func cenv cx P vs id idx saved_base base p dst sz
      ainst (if k = LENGTH vs then exit_lbl else stmts_lbl) st k es next /\
    (!x. x <> dv ==> lookup_var x next = lookup_var x cc) /\
    next.vs_allocas = cc.vs_allocas /\
    gas_marked_path F ctx func cc 0 (OK next) /\
    (!fuel rr. run_from fuel ctx func next = rr /\ (!e. rr <> Error e) ==>
       ?fuel'. run_from fuel' ctx func cc = rr)
Proof
  rpt gen_tac >> strip_tac >>
  `k <= LENGTH vs` by fs[array_loop_inv_def] >>
  `(n2w k : bytes32) = n2w (LENGTH vs) <=> k = LENGTH vs` by
    (`k < dimword (:256)` by decide_tac >> simp[n2w_11]) >>
  qexists_tac `jump_to (if k = LENGTH vs then exit_lbl else stmts_lbl)
    (update_var dv (bool_to_word (k = LENGTH vs)) cc)` >>
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
  conj_tac
  >- (`gas_marked_path F ctx func cc 0
        (OK (jump_to (if (n2w k : bytes32) = n2w (LENGTH vs) then exit_lbl
                      else stmts_lbl)
          (update_var dv (bool_to_word ((n2w k : bytes32) = n2w (LENGTH vs))) cc)))`
        suffices_by simp[] >>
      irule eq_branch_zero_path >>
      fs[array_loop_inv_def] >>
      simp[get_instruction_def, mk_inst_def, eval_operand_def]) >>
  fs[array_loop_inv_def] >> drule eq_condition_block >>
  simp[] >> disch_then (qspecl_then [`ctx`, `cc`, `n2w k`, `n2w (LENGTH vs)`] mp_tac) >>
  simp[eval_operand_def] >> gvs[n2w_11]
QED

Theorem dynarray_address_prefix_run:
  !s idx saved_base arr_base k stride ov tot ep j3 j4 j5.
  lookup_var idx s = SOME (n2w k) /\
  eval_operand saved_base s = SOME arr_base /\
  (!x. saved_base = Var x ==> x <> ov /\ x <> tot) /\ ov <> tot ==>
  run_inst_seq
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [Lit 32w; Var ov] [tot];
     mk_inst j5 ADD [saved_base; Var tot] [ep]] s =
  OK (update_var ep (n2w (w2n arr_base + 32 + k * stride))
        (update_var tot (n2w (32 + k * stride))
          (update_var ov (n2w (k * stride)) s)))
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]) s =
   OK (update_var ov (n2w (k * stride)) s)` by
    (simp[GSYM word_mul_n2w] >> irule step_MUL >> simp[eval_operand_def]) >>
  qabbrev_tac `s1 = update_var ov (n2w (k * stride)) s` >>
  `step_inst_base (mk_inst j4 ADD [Lit 32w; Var ov] [tot]) s1 =
   OK (update_var tot (n2w (32 + k * stride)) s1)` by
    (simp[GSYM word_add_n2w] >> irule step_ADD >>
     simp[Abbr `s1`, eval_operand_def, lookup_var_update_var]) >>
  qabbrev_tac `s2 = update_var tot (n2w (32 + k * stride)) s1` >>
  `eval_operand saved_base s2 = SOME arr_base` by
    (Cases_on `saved_base` >>
     gvs[Abbr `s2`, Abbr `s1`, eval_operand_def, lookup_var_update_var]) >>
  `step_inst_base (mk_inst j5 ADD [saved_base; Var tot] [ep]) s2 =
   OK (update_var ep (arr_base + n2w (32 + k * stride)) s2)` by
    (irule step_ADD >> simp[Abbr `s2`, eval_operand_def, lookup_var_update_var]) >>
  `arr_base + n2w (32 + k * stride) =
   n2w (w2n arr_base + 32 + k * stride) : bytes32` by
    (Cases_on `arr_base` >> simp[word_add_n2w, w2n_n2w]) >>
  simp[run_inst_seq_def]
QED

Theorem dynarray_for_body_entry_run:
  !ctx func cenv bc cx es s id p sz dst ainst tv v et tenv sa sb0
   idx saved_base arr_base k stride ov tot ep j3 j4 j5.
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocMemory F et et sa = ((),sb0) /\
  stride = type_memory_size tv /\ type_memory_bytes cenv et = stride /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n arr_base + 32 + k * stride) s.vs_memory /\
  w2n arr_base + 32 + k * stride < dimword (:256) /\ stride + 64 < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\ local_ptrs_reserved bc sa /\
  lookup_scopes id es.scopes = NONE /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes tot /\
  not_local_ptr cenv es.scopes ep /\
  lookup_var idx s = SOME (n2w k) /\ eval_operand saved_base s = SOME arr_base /\
  lookup_var p s = SOME dst /\ p <> ov /\ p <> tot /\ p <> ep /\ ov <> tot /\
  (!x. saved_base = Var x ==> x <> ov /\ x <> tot) /\
  not_fresh_at sa ep /\
  MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
  ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\ stride <= sz ==>
  ?t. run_inst_seq
    ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
      mk_inst j4 ADD [Lit 32w; Var ov] [tot];
      mk_inst j5 ADD [saved_base; Var tot] [ep]] ++ emitted_insts sa sb0) s = OK t /\
    stmt_state_rel ctx func bc cx
      (es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes) t /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep ==>
      lookup_var x t = lookup_var x s) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb0)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `s1 = update_var ep (n2w (w2n arr_base + 32 + k * stride))
    (update_var tot (n2w (32 + k * stride))
      (update_var ov (n2w (k * stride)) s))` >>
  `run_inst_seq [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [Lit 32w; Var ov] [tot];
     mk_inst j5 ADD [saved_base; Var tot] [ep]] s = OK s1` by
    (qunabbrev_tac `s1` >> irule dynarray_address_prefix_run >> simp[] >>
     metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx es s1` by
    (simp[Abbr `s1`] >> irule stmt_state_rel_update_var >> simp[] >>
     irule stmt_state_rel_update_var >> simp[] >>
     irule stmt_state_rel_update_var >> simp[]) >>
  `stmt_state_rel ctx func bc cx (es with scopes := FEMPTY :: es.scopes) s1` by
    (irule array_empty_scope_rel_transport >> qexists_tac `cenv` >> simp[]) >>
  `not_fresh_at sa p` by metis_tac[array_copy_live_ptrs_reserved] >>
  `!x. Var ep = Var x ==> not_fresh_at sa x` by simp[] >>
  `!x. Var p = Var x ==> not_fresh_at sa x` by simp[] >>
  `eval_operand (Var ep) s1 = SOME (n2w (w2n arr_base + 32 + k * stride)) /\
   eval_operand (Var p) s1 = SOME dst` by
    fs[Abbr `s1`, eval_operand_def, lookup_var_update_var] >>
  `val_in_memory tv v
     (w2n (n2w (w2n arr_base + 32 + k * stride) : bytes32)) s1.vs_memory` by
    gvs[Abbr `s1`, update_var_def, w2n_n2w] >>
  `type_memory_bytes cenv et = type_memory_size tv /\
   type_memory_size tv + 64 < dimword (:256)` by metis_tac[] >>
  drule_all array_iter_copy_run >> strip_tac >>
  `lookup_var p s1 = SOME dst /\
   FLOOKUP s1.vs_allocas ainst.inst_id = SOME (w2n dst,sz)` by
    (qpat_x_assum `lookup_var p s = SOME dst` mp_tac >>
     simp[Abbr `s1`, lookup_var_update_var, update_var_def]) >>
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
  >- (qpat_assum `run_inst_seq [_;_;_] s = OK s1`
        (mp_then Any (qspec_then `emitted_insts sa sb0` mp_tac) run_inst_seq_append) >>
      gvs[]) >>
  simp[] >> conj_tac
  >- (qpat_x_assum `(t with <|vs_vars := _; vs_memory := _|>) = s1` mp_tac >>
      simp[Abbr `s1`, update_var_def] >>
      POP_ASSUM_LIST (K all_tac) >>
      simp[venom_state_component_equality] >> strip_tac >> gvs[]) >>
  rpt strip_tac >> first_x_assum drule >>
  simp[Abbr `s1`, lookup_var_update_var]
QED

Theorem dynarray_ret_pc_copy_frame[local]:
  ret_pc_ok bc st s /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!x. not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep ==>
    lookup_var x t = lookup_var x s) ==>
  ret_pc_ok bc st t
Proof
  rw[ret_pc_ok_def] >>
  `not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep` by metis_tac[] >>
  first_x_assum drule >> simp[] >> metis_tac[]
QED

(* What the copy prefix leaves at the start of the body statements. *)
Definition dynarray_entry_ready_def:
  dynarray_entry_ready ctx func bc cx es id tv v sb0 sa ov tot ep st s s2 <=>
  s2.vs_current_bb = sb0.cs_current_bb /\
  s2.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ~s2.vs_halted /\
  stmt_state_rel ctx func bc cx
    (es with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes) s2 /\
  ret_pc_ok bc st s2 /\ s2.vs_allocas = s.vs_allocas /\
  (!x. not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep ==>
    lookup_var x s2 = lookup_var x s) /\
  gas_marked_path F ctx func s 0 (OK s2) /\
  (!fuel. run_from fuel ctx func s = run_from fuel ctx func s2)
End

Theorem dynarray_for_body_entry:
  !ctx func cenv bc cx es s id p sz dst ainst tv v et tenv sa sb0
   idx saved_base arr_base k stride ov tot ep j3 j4 j5 bb st.
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocMemory F et et sa = ((),sb0) /\
  stride = type_memory_size tv /\ type_memory_bytes cenv et = stride /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n arr_base + 32 + k * stride) s.vs_memory /\
  w2n arr_base + 32 + k * stride < dimword (:256) /\ stride + 64 < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\ local_ptrs_reserved bc sa /\
  lookup_scopes id es.scopes = NONE /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes tot /\
  not_local_ptr cenv es.scopes ep /\
  lookup_var idx s = SOME (n2w k) /\ eval_operand saved_base s = SOME arr_base /\
  lookup_var p s = SOME dst /\ p <> ov /\ p <> tot /\ p <> ep /\ ov <> tot /\
  (!x. saved_base = Var x ==> x <> ov /\ x <> tot) /\ not_fresh_at sa ep /\
  MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
  ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\ stride <= sz /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  sb0.cs_current_insts =
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [Lit 32w; Var ov] [tot];
     mk_inst j5 ADD [saved_base; Var tot] [ep]] ++ emitted_insts sa sb0 /\
  s.vs_current_bb = sb0.cs_current_bb /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  ret_pc_ok bc st s /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) ==>
  ?s2. dynarray_entry_ready ctx func bc cx es id tv v sb0 sa ov tot ep st s s2
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[dynarray_entry_ready_def] >>
  mp_tac (SPEC_ALL dynarray_for_body_entry_run) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  `run_inst_seq sb0.cs_current_insts s = OK t` by metis_tac[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    sb0.cs_current_insts` by
    simp[mk_inst_def, is_terminator_def] >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb0)` by
    (irule iter_memory_copy_no_gas >> goal_assum (drule_at Any)) >>
  `EVERY (\i. i.inst_opcode <> GAS) sb0.cs_current_insts` by
    simp[mk_inst_def] >>
  `sb0.cs_current_insts = sb0.cs_current_insts` by simp[] >>
  drule_all array_body_prefix_continuation >> strip_tac >>
  `ret_pc_ok bc st t` by
    (mp_tac dynarray_ret_pc_copy_frame >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  qexists_tac `s2` >> simp[] >>
  `!x. lookup_var x s2 = lookup_var x t` by simp[lookup_var_def] >>
  conj_tac
  >- (fs[ret_pc_ok_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem dynarray_round_body_prepare:
  dynarray_entry_ready ctx func bc cx es id tv v sb0 sa ov tot ep sb0 s s2 /\
  gas_marked_path F ctx func cc 0 (OK s) /\
  ei = es with <|scopes :=
    (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
      :: es.scopes; gas_obs := []|> /\
  stmt_frag ctx func cx lctx RetQ bc m source ei /\
  m sb0 = (bc',sb1) /\ fn_has_code sb0 sb1 func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved bc sb0 /\
  ~block_is_terminated sb0 /\ gas_admissible source (stmt_res_ok lctx) ei ==>
  gas_marked_exec F (ctx,func) (push_scope_with_var id tv v) (es,cc) []
    (INL ())
    (es with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
        :: es.scopes) (OK s2) /\
  gas_outcome F (cx_tops cx) (ctx,func) source (ei,s2)
    (stmt_post ctx func cx lctx bc bc' sb0 sb1 s2)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >>
  `gas_marked_path F ctx func cc 0 (OK s2)` by
    (fs[dynarray_entry_ready_def] >>
     drule_all gas_marked_path_then >> simp[]) >>
  (conj_tac >- (irule push_scope_with_var_zero_exec >> simp[])) >>
  qpat_x_assum `stmt_frag _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[stmt_frag_def, stmt_framed_frag_def] >>
  disch_then irule >> simp[] >>
  fs[dynarray_entry_ready_def] >>
  `!E. stmt_state_rel ctx func bc cx E s2 ==>
       stmt_state_rel ctx func bc cx (E with gas_obs := []) s2` by
    (rpt strip_tac >>
     `s2 = s2 with <|vs_gas_readings := s2.vs_gas_readings;
                     vs_inst_idx := s2.vs_inst_idx|>` by
       simp[venomStateTheory.venom_state_component_equality] >>
     pop_assum SUBST1_TAC >> irule msg_gas_state_frame >> simp[]) >>
  first_x_assum (qspec_then `es with scopes :=
    (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
      :: es.scopes` mp_tac) >>
  impl_tac >- fs[] >>
  match_mp_tac EQ_IMPLIES >> AP_THM_TAC >> AP_TERM_TAC >>
  simp[vyperStateTheory.evaluation_state_component_equality]
QED

Theorem dynarray_entry_ready_runtime:
  dynarray_entry_ready ctx func bc cx es id tv v sb0 sa ov tot ep sb0 s s2 /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst lbl st k es s /\
  not_fresh_at sa idx /\ idx <> ov /\ idx <> tot /\ idx <> ep /\
  not_fresh_at sa p /\ p <> ov /\ p <> tot /\ p <> ep /\
  (!x. saved_base = Var x ==>
     not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!l. saved_base <> Label l) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) ==>
  lookup_var idx s2 = SOME (n2w k) /\
  eval_operand saved_base s2 = SOME arr_base /\ lookup_var p s2 = SOME dst /\
  FLOOKUP s2.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
  ret_pc_ok cenv st s2
Proof
  strip_tac >>
  `ret_pc_ok cenv st s2` by
    (mp_tac (Q.INST [`bc` |-> `cenv`, `t` |-> `s2`] dynarray_ret_pc_copy_frame) >>
     impl_tac >- fs[dynarray_entry_ready_def, array_loop_inv_def] >>
     simp[]) >>
  fs[dynarray_entry_ready_def, array_loop_inv_def] >>
  irule array_saved_operand_frame >> metis_tac[]
QED

Theorem dynarray_for_code_iteration_static:
  dynarray_for_code func cenv bc ty stmts id et tv stride saved_base
    p sz ainst idx dv ov tot ep nv lv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj ==>
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
  not_fresh_at sa idx /\ idx <> ov /\ idx <> tot /\ idx <> ep /\
  not_fresh_at sa p /\ p <> ov /\ p <> tot /\ p <> ep /\
  (!x. saved_base = Var x ==>
     not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep)
Proof
  simp[dynarray_for_code_def, ALL_DISTINCT] >> metis_tac[]
QED

Theorem dynarray_for_code_entry_static:
  dynarray_for_code func cenv bc ty stmts id et tv stride saved_base
    p sz ainst idx dv ov tot ep nv lv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj ==>
  (!scs. not_local_ptr cenv scs dv) /\ dv <> idx /\ dv <> p /\
  (!x. saved_base = Var x ==> x <> dv) /\
  lookup_block cond_lbl func.fn_blocks =
    SOME <| bb_label := cond_lbl;
            bb_instructions :=
              [mk_inst j1 EQ [Var idx; Var lv] [dv];
               mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []] |>
Proof
  simp[dynarray_for_code_def, ALL_DISTINCT] >> metis_tac[]
QED

(* The copy entry's static inputs, read off the emitted code. *)
Theorem dynarray_for_code_entry_inputs:
  dynarray_for_code func cenv bc ty stmts id et tv stride saved_base
    p sz ainst idx dv ov tot ep nv lv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj ==>
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocMemory F et et sa = ((),sb0) /\
  stride = type_memory_size tv /\ type_memory_bytes cenv et = stride /\
  stride + 64 < dimword (:256) /\ local_ptrs_reserved bc sa /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  (!scs. not_local_ptr cenv scs ov /\ not_local_ptr cenv scs tot /\
         not_local_ptr cenv scs ep) /\
  p <> ov /\ p <> tot /\ p <> ep /\ ov <> tot /\
  (!x. saved_base = Var x ==> x <> ov /\ x <> tot) /\ not_fresh_at sa ep /\
  MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
  ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\ stride <= sz /\
  sb0.cs_current_insts =
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [Lit 32w; Var ov] [tot];
     mk_inst j5 ADD [saved_base; Var tot] [ep]] ++ emitted_insts sa sb0 /\
  sb0.cs_current_bb = stmts_lbl /\
  compile_stmts bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = ((),sb1) /\
  (~block_is_terminated sb1 ==>
     sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
     sj.cs_current_insts = sb1.cs_current_insts ++
       [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\
     fn_has_code sb1 sj func)
Proof
  simp[dynarray_for_code_def, ALL_DISTINCT] >> rpt strip_tac >> gvs[]
QED

Theorem dynarray_body_finish_counted:
  dynarray_for_code func cenv bc ty stmts id et tv stride saved_base
    p sz ainst idx dv ov tot ep nv lv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj /\ k < LENGTH vs /\
  gas_marked_exec F (ctx,func) (eval_stmts cx stmts) (entry,s2) marks res ee (OK t) /\
  stmt_post ctx func cx (InLoop exit_lbl incr_lbl) bc bc' sb0 sb1 s2
    res (ee with gas_obs := []) t /\
  cenv_top_ext cenv bc entry.scopes /\
  (!gs r es2. eval_stmts cx stmts (entry with gas_obs := gs) = (r,es2) ==>
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\
        lookup_scopes id rest = NONE)) /\
  lookup_var idx s2 = SOME (n2w k) /\ lookup_var p s2 = SOME dst /\
  eval_operand saved_base s2 = SOME arr_base /\
  FLOOKUP s2.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
  ret_pc_ok bc sb0 s2 /\ ret_pc_ok cenv st s2 /\
  not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
  (!x. saved_base = Var x ==> not_fresh_at sb0 x) /\
  (!l. saved_base <> Label l) /\
  (!x. not_fresh_at caller x ==> not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
  array_caller_frame caller cc s2 ==>
  ?rest u. ee.scopes <> [] /\ rest = TL ee.scopes /\
    gas_marked_path F ctx func t 0 (OK u) /\ array_caller_frame caller cc u /\
    ((res = INR BreakException /\ u.vs_current_bb = exit_lbl /\
      u.vs_inst_idx = 0 /\ ~u.vs_halted /\
      stmt_state_rel ctx func cenv cx
        (ee with <|scopes := rest; gas_obs := []|>) u) \/
     ((res = INL () \/ res = INR ContinueException) /\
      array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
        ainst cond_lbl st (SUC k) (ee with <|scopes := rest; gas_obs := []|>) u))
Proof
  strip_tac >> drule_all array_body_counted_post >> strip_tac >>
  `array_caller_frame caller cc t` by
    (fs[array_caller_frame_def] >> metis_tac[]) >>
  Cases_on `res = INR BreakException`
  >- (qexistsl_tac [`rest`, `t`] >>
      fs[stmt_lands_def, gas_marked_path_def, gas_path_rules]) >>
  `res = INL () \/ res = INR ContinueException` by fs[stmt_lands_def] >>
  drule_all array_body_runtime_frame >> strip_tac >>
  `~t.vs_halted /\ stmt_state_rel ctx func cenv cx
      (ee with <|scopes := rest; gas_obs := []|>) t` by fs[] >>
  `array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst t.vs_current_bb st k (ee with <|scopes := rest; gas_obs := []|>)
    (t with vs_inst_idx := 0)` by
      (fs[array_loop_inv_def, stmt_state_rel_inst_idx, lookup_var_def,
           ret_pc_ok_def] >>
       Cases_on `saved_base` >> gvs[eval_operand_def, lookup_var_def]) >>
  drule dynarray_for_code_iteration_static >> strip_tac >>
  drule dynarray_for_code_entry_inputs >> strip_tac >>
  qhdtm_x_assum `dynarray_for_code` kall_tac >>
  `?next. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst cond_lbl st (k+1) (ee with <|scopes := rest; gas_obs := []|>) next /\
     (!x. x <> idx /\ x <> nv ==> lookup_var x next = lookup_var x t) /\
     next.vs_allocas = t.vs_allocas /\ gas_marked_path F ctx func t 0 (OK next)` by
    (irule array_body_continue_iteration_framed >> simp[] >>
     goal_assum (drule_at (Pat `lookup_block _ _ = _`)) >>
     goal_assum (drule_at (Pat `stmt_lands _ _ _ _`)) >>
     qexists_tac `sj` >> simp[]) >>
  qexistsl_tac [`rest`, `next`] >> simp[arithmeticTheory.ADD1] >>
  fs[array_caller_frame_def] >> metis_tac[]
QED

Theorem dynarray_round_prepare:
  dynarray_for_code func cenv bc ty stmts id et tv stride saved_base
    p sz ainst idx dv ov tot ep nv lv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond_lbl st k es cc /\
  lookup_var lv cc = SOME (n2w (LENGTH vs)) /\
  k < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv (EL k vs) /\
  val_wf tv (EL k vs) /\ w2n arr_base + 32 + k * stride < dimword (:256) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  (!s. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst stmts_lbl st k es s ==>
     val_in_memory tv (EL k vs) (w2n arr_base + 32 + k * stride) s.vs_memory /\
     ret_pc_ok bc sb0 s) /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!x. not_fresh_at caller x ==>
    not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!l. saved_base <> Label l) /\
  entry = es with <|scopes := (FEMPTY |+ (id,
    <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes;
    gas_obs := []|> /\
  stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
    (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts) entry /\
  gas_admissible (eval_stmts cx stmts) (stmt_res_ok (InLoop exit_lbl incr_lbl)) entry ==>
  ?s2 bc'.
    stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = (bc',sb1) /\
    ret_pc_ok bc sb0 s2 /\ ret_pc_ok cenv st s2 /\
    lookup_var idx s2 = SOME (n2w k) /\ lookup_var p s2 = SOME dst /\
    eval_operand saved_base s2 = SOME arr_base /\
    FLOOKUP s2.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
    array_caller_frame caller cc s2 /\
    gas_marked_exec F (ctx,func) (push_scope_with_var id tv (EL k vs))
      (es,cc) [] (INL ())
      (es with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes)
      (OK s2) /\
    gas_outcome F (cx_tops cx) (ctx,func) (eval_stmts cx stmts) (entry,s2)
      (stmt_post ctx func cx (InLoop exit_lbl incr_lbl) bc bc' sb0 sb1 s2)
      (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >>
  drule dynarray_for_code_entry_static >> strip_tac >>
  `not_local_ptr cenv es.scopes dv` by metis_tac[] >>
  drule_all dynarray_condition_boundary >> strip_tac >>
  rename1 `array_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s` >>
  `k <> LENGTH vs` by decide_tac >> gvs[] >>
  `cenv_top_ext cenv bc (FEMPTY :: es.scopes)` by
    (irule dynarray_for_code_scope_frame >> fs[array_loop_inv_def] >> metis_tac[]) >>
  first_x_assum drule >> strip_tac >>
  drule dynarray_for_code_iteration_static >> strip_tac >>
  drule dynarray_for_code_entry_inputs >> strip_tac >>
  `?s2. dynarray_entry_ready ctx func bc cx es id tv (EL k vs) sb0 sa ov tot ep
          sb0 s s2` by
    (irule dynarray_for_body_entry >>
     fs[array_loop_inv_def] >> gvs[] >>
     qexistsl_tac [`ainst`, `arr_base`, `cenv`, `et`, `idx`, `j3`, `j4`, `j5`,
                   `k`, `saved_base`, `tenv`] >>
     simp[] >> metis_tac[]) >>
  `?bc'. stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = (bc',sb1)` by
    (irule array_body_compiler_env >> simp[]) >>
  qmatch_asmsub_abbrev_tac `stmt_frag _ _ _ _ _ _ _ _ entry` >>
  `entry = es with <|scopes := (FEMPTY |+ (id,
    <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes;
    gas_obs := []|>` by simp[Abbr `entry`] >>
  qhdtm_x_assum `dynarray_for_code` kall_tac >>
  drule_all dynarray_round_body_prepare >> strip_tac >>
  drule_all dynarray_entry_ready_runtime >> strip_tac >>
  qexistsl_tac [`s2`, `bc'`] >> simp[] >>
  qhdtm_x_assum `dynarray_entry_ready` mp_tac >>
  qpat_x_assum `!x. not_fresh_at caller x ==> _` mp_tac >>
  qpat_x_assum `!x. x <> dv ==> _` mp_tac >>
  qpat_x_assum `s.vs_allocas = _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  pure_rewrite_tac[dynarray_entry_ready_def, array_caller_frame_def] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem dynarray_for_round_counted:
  dynarray_for_code func cenv bc ty stmts id et tv stride saved_base
    p sz ainst idx dv ov tot ep nv lv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond_lbl st k es cc /\
  lookup_var lv cc = SOME (n2w (LENGTH vs)) /\
  k < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv (EL k vs) /\
  val_wf tv (EL k vs) /\ w2n arr_base + 32 + k * stride < dimword (:256) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  (!s. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst stmts_lbl st k es s ==>
     val_in_memory tv (EL k vs) (w2n arr_base + 32 + k * stride) s.vs_memory /\
     ret_pc_ok bc sb0 s) /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!x. not_fresh_at caller x ==>
    not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!x. not_fresh_at caller x ==> not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
  not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
  (!x. saved_base = Var x ==> not_fresh_at sb0 x) /\ (!l. saved_base <> Label l) /\
  entry = es with <|scopes := (FEMPTY |+ (id,
    <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes;
    gas_obs := []|> /\
  stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
    (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts) entry /\
  (!gs r es2. eval_stmts cx stmts (entry with gas_obs := gs) = (r,es2) ==>
    stmt_res_ok (InLoop exit_lbl incr_lbl) r /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\
        lookup_scopes id rest = NONE)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (do push_scope_with_var id tv (EL k vs);
        finally (try (do eval_stmts cx stmts; return F od) handle_loop_exception)
          pop_scope od) (es,cc)
    (\res ee t. ?broke. res = INL broke /\ array_caller_frame caller cc t /\
      (broke ==> t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
        stmt_state_rel ctx func cenv cx ee t) /\
      (~broke ==> array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base
        p dst sz ainst cond_lbl st (SUC k) ee t))
    (\res ee r. ?ex. res = INR ex /\
      !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) r)
Proof
  strip_tac >>
  `gas_admissible (eval_stmts cx stmts)
    (stmt_res_ok (InLoop exit_lbl incr_lbl)) entry` by
    (qpat_x_assum `!gs r es2. _` mp_tac >>
     rpt (pop_assum kall_tac) >> rewrite_tac[gas_admissible_def] >> metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `gas_outcome F (cx_tops cx) (ctx,func) round (es,cc) Q R` >>
  drule_all dynarray_round_prepare >> strip_tac >>
  qhdtm_x_assum `stmt_frag` kall_tac >>
  qhdtm_x_assum `gas_outcome` mp_tac >> rewrite_tac[gas_outcome_def] >> strip_tac
  >- suspend "ordinary"
  >> suspend "exempt"
QED

Resume dynarray_for_round_counted[exempt]:
  `?sc rest. ee.scopes = sc :: rest` by
    (drule gas_exempt_cert_execution >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >>
     simp[ignore_bind_def, bind_def, return_def, AllCaseEqs()] >> strip_tac >>
     qpat_x_assum `!gs r es2. _`
       (qspec_then `gas_explicit marks s2.vs_gas_readings` mp_tac) >>
     gvs[] >> strip_tac >> goal_assum (drule_at Any)) >>
  gvs[] >>
  drule_all loop_round_exempt_cert >> strip_tac >>
  qexists_tac `marks` >> disj2_tac >>
  simp[Abbr `round`] >> goal_assum (drule_at Any)
QED

Resume dynarray_for_round_counted[ordinary]:
  qhdtm_x_assum `gas_summary_at` mp_tac >>
  rewrite_tac[gas_summary_at_def] >>
  disch_then (qx_choose_then `res` (qx_choose_then `ee`
    (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)))) >>
  `?sc rest. ee.scopes = sc :: rest` by
    (qhdtm_assum `gas_marked_exec` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` assume_tac) >>
     qpat_x_assum `!gs r es2. _`
       (qspec_then `gas_explicit marks s2.vs_gas_readings` mp_tac) >>
     gvs[] >> strip_tac >> goal_assum (drule_at Any)) >>
  drule_all loop_body_cleanup_exec >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_marked_exec F (ctx,func) cleanup _ _ wrapped fin r` >>
  `gas_marked_exec F (ctx,func) round (es,cc) marks wrapped fin r` by
    (simp[Abbr `round`, ignore_bind_def] >>
     irule (SRULE [] (Q.INST [`left` |-> `[]`] gas_marked_exec_bind_normal)) >>
     goal_assum (drule_at Any) >> gvs[]) >>
  strip_tac >- suspend "normal_finish" >> suspend "exit_finish"
QED

Resume dynarray_for_round_counted[exit_finish]:
  fs[] >>
  `res <> INL () /\ res <> INR BreakException /\ res <> INR ContinueException` by
    (qpat_x_assum `!tail. stmt_exit _ _ _ _` (qspec_then `[]` mp_tac) >>
     metis_tac[stmt_exit_loop_ctl]) >>
  Cases_on `res` >- gvs[] >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`wrapped`, `fin`, `r`] >> simp[] >> disj2_tac >>
  gvs[Abbr `R`, Abbr `fin`, Abbr `wrapped`, stmt_exit_def]
QED

Resume dynarray_for_round_counted[normal_finish]:
  fs[] >>
  `cenv_top_ext cenv bc entry.scopes` by
    (drule dynarray_for_code_scope_frame >>
     fs[array_loop_inv_def, cenv_top_ext_def] >> metis_tac[]) >>
  `!gs r es2. eval_stmts cx stmts (entry with gas_obs := gs) = (r,es2) ==>
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\
        lookup_scopes id rest = NONE)` by
    (qpat_x_assum `!gs r es2. _` mp_tac >> rpt (pop_assum kall_tac) >> metis_tac[]) >>
  drule_all dynarray_body_finish_counted >> strip_tac >>
  `gas_marked_exec F (ctx,func) round (es,cc) marks wrapped fin (OK u)` by
    (qhdtm_x_assum `gas_marked_path` mp_tac >>
     qpat_x_assum `gas_marked_exec _ _ round _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> rewrite_tac[gas_marked_exec_def] >>
     rpt strip_tac >> simp[] >>
     qpat_x_assum `gas_marked_path _ _ _ cc _ _` mp_tac >>
     disch_then (mp_then Any mp_tac gas_marked_path_then) >>
     disch_then drule >> simp[]) >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`wrapped`, `fin`, `OK u`] >> simp[] >> disj1_tac >>
  simp[Abbr `Q`, Abbr `fin`, Abbr `wrapped`] >>
  gvs[]
QED
Finalise dynarray_for_round_counted

Theorem dynarray_loop_last_counted:
  dynarray_for_code func cenv bc ty stmts id et tv stride saved_base
    p sz ainst idx dv ov tot ep nv lv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond_lbl st (LENGTH vs) es s /\
  lookup_var lv s = SOME (n2w (LENGTH vs)) /\ LENGTH vs < dimword (:256) /\
  (!x. not_fresh_at caller x ==> x <> dv) /\ array_caller_frame caller old s ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    stmt_state_rel ctx func cenv cx (es with gas_obs := []) t /\
    array_caller_frame caller old t
Proof
  strip_tac >> drule dynarray_for_code_entry_static >> strip_tac >>
  `not_local_ptr cenv es.scopes dv` by simp[] >>
  drule_all dynarray_condition_boundary >> simp[] >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) next` by
    (fs[array_loop_inv_def] >> drule msg_gas_state_frame >>
     disch_then (qspecl_then [`next.vs_gas_readings`, `next.vs_inst_idx`, `[]`] mp_tac) >>
     simp[stmt_state_rel_inst_idx]) >>
  qexists_tac `next` >> fs[array_loop_inv_def] >>
  fs[array_caller_frame_def] >> metis_tac[]
QED

Theorem dynarray_for_loop_counted:
  dynarray_for_code func cenv bc ty stmts id et tv stride saved_base
    p sz ainst idx dv ov tot ep nv lv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj /\
  LENGTH vs < dimword (:256) /\ evaluate_type tenv et = SOME tv /\
  (!j. j < LENGTH vs ==> value_has_type tv (EL j vs) /\ val_wf tv (EL j vs)) /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  (!j ei s. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst stmts_lbl st j ei s /\ j < LENGTH vs ==>
     val_in_memory tv (EL j vs) (w2n arr_base + 32 + j * stride) s.vs_memory /\
     ret_pc_ok bc sb0 s) /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!x. not_fresh_at caller x ==>
    not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!x. not_fresh_at caller x ==> not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
  not_fresh_at caller lv /\ lookup_var lv old = SOME (n2w (LENGTH vs)) /\
  not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
  (!x. saved_base = Var x ==> not_fresh_at sb0 x) /\ (!l. saved_base <> Label l) /\
  (!ei j. P ei /\ lookup_scopes id ei.scopes = NONE /\ j < LENGTH vs ==>
    w2n arr_base + 32 + j * stride < dimword (:256) /\
    not_local_ptr bc (FEMPTY :: ei.scopes) p /\
    stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
      (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
      (ei with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL j vs; popped := []|>)) :: ei.scopes;
        gas_obs := []|>) /\
    (!gs r es2. eval_stmts cx stmts
      (ei with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL j vs; popped := []|>)) :: ei.scopes;
        gas_obs := gs|>) = (r,es2) ==>
      stmt_res_ok (InLoop exit_lbl incr_lbl) r /\
      ?sc rest. es2.scopes = sc :: rest /\
        (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
        ((r = INL () \/ r = INR ContinueException) ==>
          P (es2 with scopes := rest) /\
          lookup_scopes id rest = NONE))) /\
  k <= LENGTH vs /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond_lbl st k es cc /\ array_caller_frame caller old cc /\
  gas_admissible (eval_for cx tv id stmts (DROP k vs)) (stmt_res_ok lctx) es ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_for cx tv id stmts (DROP k vs)) (es,cc)
    (\res ee t. res = INL () /\ t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\
      ~t.vs_halted /\ stmt_state_rel ctx func cenv cx ee t /\
      array_caller_frame caller old t)
    (\res ee r. ?ex. res = INR ex /\
      !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) r)
Proof
  strip_tac >>
  qabbrev_tac `Inv = \j ei s.
    array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
      ainst cond_lbl st j ei s /\ array_caller_frame caller old s` >>
  qabbrev_tac `Done = \ei s. s.vs_current_bb = exit_lbl /\ s.vs_inst_idx = 0 /\
    ~s.vs_halted /\ stmt_state_rel ctx func cenv cx ei s /\
    array_caller_frame caller old s` >>
  qabbrev_tac `R = \ex ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) r` >>
  `(!j ei s. j < LENGTH vs /\ Inv j ei s /\
      gas_admissible (eval_for cx tv id stmts (DROP j vs)) (stmt_res_ok lctx) ei ==>
      gas_outcome F (cx_tops cx) (ctx,func)
        (do push_scope_with_var id tv (EL j vs);
            finally (try (do eval_stmts cx stmts; return F od)
              handle_loop_exception) pop_scope od) (ei,s)
        (\res ee t. ?broke. res = INL broke /\
          (broke ==> Done ee t) /\ (~broke ==> Inv (SUC j) ee t))
        (\res ee r. ?ex. res = INR ex /\ R ex ee r)) /\
    (!ei s. Inv (LENGTH vs) ei s ==>
      ?t. gas_marked_path F ctx func s 0 (OK t) /\ Done (ei with gas_obs := []) t)` by
    (conj_tac >- suspend "round" >> suspend "last") >>
  drule eval_for_rounds >>
  disch_then (qspecl_then [`k`, `es`, `cc`] mp_tac) >>
  simp[Abbr `Inv`, Abbr `Done`, Abbr `R`]
QED

Resume dynarray_for_loop_counted[last]:
  rpt gen_tac >> simp[Abbr `Inv`, Abbr `Done`] >> strip_tac >>
  `!x. not_fresh_at caller x ==> x <> dv` by metis_tac[] >>
  `lookup_var lv s = SOME (n2w (LENGTH vs))` by
    fs[array_caller_frame_def] >>
  drule_all dynarray_loop_last_counted >> simp[]
QED

Resume dynarray_for_loop_counted[round]:
  rpt gen_tac >> simp[Abbr `Inv`] >> strip_tac >>
  `P ei /\ lookup_scopes id ei.scopes = NONE` by fs[array_loop_inv_def] >>
  `lookup_var lv s = SOME (n2w (LENGTH vs))` by
    fs[array_caller_frame_def] >>
  qpat_assum `!ei j. _` drule_all >> strip_tac >>
  `value_has_type tv (EL j vs) /\ val_wf tv (EL j vs)` by metis_tac[] >>
  qabbrev_tac `entry = ei with <|scopes := (FEMPTY |+ (id,
    <|assignable := F; type := tv; value := EL j vs; popped := []|>)) :: ei.scopes;
    gas_obs := []|>` >>
  `!gs r es2. eval_stmts cx stmts (entry with gas_obs := gs) = (r,es2) ==>
    stmt_res_ok (InLoop exit_lbl incr_lbl) r /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\
        lookup_scopes id rest = NONE)` by
    (qpat_x_assum `!gs r es2. _` mp_tac >> simp[Abbr `entry`]) >>
  `!t. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
      ainst stmts_lbl st j ei t ==>
    val_in_memory tv (EL j vs) (w2n arr_base + 32 + j * stride) t.vs_memory /\
    ret_pc_ok bc sb0 t` by metis_tac[] >>
  `entry = ei with <|scopes := (FEMPTY |+ (id,
    <|assignable := F; type := tv; value := EL j vs; popped := []|>)) :: ei.scopes;
    gas_obs := []|>` by simp[Abbr `entry`] >>
  drule_all dynarray_for_round_counted >> strip_tac >>
  qhdtm_x_assum `gas_outcome` mp_tac >>
  qpat_x_assum `array_caller_frame caller old s` mp_tac >>
  simp[Abbr `Done`, Abbr `R`, NoAsms] >>
  rpt (pop_assum kall_tac) >> strip_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac)
  >- (qexists_tac `marks` >> disj1_tac >>
      qhdtm_x_assum `gas_summary_at` mp_tac >>
      rewrite_tac[gas_summary_at_def] >> strip_tac >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >>
      suspend "round_post") >>
  qexists_tac `marks` >> disj2_tac >> goal_assum (drule_at Any)
QED
Resume dynarray_for_loop_counted[round_post]:
  markerLib.RESUME_TAC >> gvs[] >>
  `array_caller_frame caller old t` by
    (irule array_caller_frame_trans >> goal_assum (drule_at Any) >> simp[]) >>
  simp[]
QED
Finalise dynarray_for_loop_counted
