(* Finite dynamic-array address and checked element installation. *)
Theory forPtrDynArrayPrepare
Ancestors forPtrArrayInvariant stmtSimForArrayLoop fragGasSeqPtr forPtrBytes forPtrArrayPrepare forPtrAddress whitelistForIterDynLoop
  bodyPtrBopInElementLoad forPtrRangePrepare bodyPtrDefs
  venomState venomInst ptrDiscipline finite_map fragExec
  exprLoweringProps compileEnv loweringStateRelDefs loweringPosts stmtFragPtr
  venomExecSemantics fragGasPathPtr assignTuplePtrCopyEndpoint

Theorem for_dynarray_address_path_ptr:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst j4 ADD [Lit 32w; Var ov] [tot]) /\
  get_instruction bb (SUC (SUC s.vs_inst_idx)) =
    SOME (mk_inst j5 ADD [Var bp; Var tot] [ep]) /\
  lookup_var idx s = SOME (n2w k) /\ lookup_var bp s = SOME w /\
  op_taint tn (Var idx) = {} /\ op_taint tn (Var bp) = {} /\
  bp <> ov /\ bp <> tot /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (set_prov (DRESTRICT (DRESTRICT G (COMPL {ov})) (COMPL {tot}))
      [ep] (FLOOKUP G bp))
    (tn with t_var := ((tn.t_var |+ (ov,{})) |+ (tot,{})) |+ (ep,{}))
    (OK ((update_var ep (w + (32w + n2w k * n2w stride))
      (update_var tot (32w + n2w k * n2w stride)
        (update_var ov (n2w k * n2w stride) s)))
      with vs_inst_idx := SUC (SUC (SUC s.vs_inst_idx))))
Proof
  strip_tac >>
  `gas_path_ptr D 0 ctx func PG G tn s 0
    (DRESTRICT G (COMPL {ov})) (tn with t_var := tn.t_var |+ (ov,{}))
    (OK ((update_var ov (n2w k * n2w stride) s)
      with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule for_mul_scalar_path_ptr >> simp[] >> metis_tac[]) >>
  qabbrev_tac `sm = (update_var ov (n2w k * n2w stride) s)
    with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `tm = tn with t_var := tn.t_var |+ (ov,{})` >>
  qabbrev_tac `Gm = DRESTRICT G (COMPL {ov})` >>
  `?Gh. gas_path_ptr D 0 ctx func PG Gm tm sm 0 Gh
    (tm with t_var := tm.t_var |+ (tot,{}))
    (OK (update_var tot (32w + n2w k * n2w stride) sm
      with vs_inst_idx := SUC sm.vs_inst_idx)) /\
    Gh = step_prov PG Gm (mk_inst j4 ADD [Lit 32w; Var ov] [tot])
      (update_var tot (32w + n2w k * n2w stride) sm) /\
    (!x. x <> tot ==> FLOOKUP Gh x = FLOOKUP Gm x)` by
    (irule membership_address_binop_path >>
     simp[Abbr `sm`, Abbr `tm`, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, op_taint_def, eval_operand_def] >>
     qexistsl_tac [`bb`, `j4`] >> simp[]) >>
  pop_assum strip_assume_tac >>
  `Gh = DRESTRICT Gm (COMPL {tot})` by
    simp[Abbr `Gm`, step_prov_def, out_prov_def, first_prov_def,
      op_prov_def, mk_inst_def, FLOOKUP_DRESTRICT, set_prov_def] >>
  qabbrev_tac `sh = update_var tot (32w + n2w k * n2w stride) sm
    with vs_inst_idx := SUC sm.vs_inst_idx` >>
  qabbrev_tac `th = tm with t_var := tm.t_var |+ (tot,{})` >>
  `FLOOKUP Gh bp = FLOOKUP G bp` by
    simp[Abbr `Gm`, FLOOKUP_DRESTRICT] >>
  `gas_path_ptr D 0 ctx func PG Gh th sh 0
    (set_prov Gh [ep] (FLOOKUP Gh bp))
    (th with t_var := th.t_var |+ (ep,{}))
    (OK (update_var ep (w + (32w + n2w k * n2w stride)) sh
      with vs_inst_idx := SUC sh.vs_inst_idx))` by
    (irule for_dynamic_add_path_ptr >>
     simp[Abbr `sh`, Abbr `th`, Abbr `sm`, Abbr `tm`, Abbr `Gm`,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
       op_taint_def] >>
     gvs[lookup_var_def, op_taint_def] >> qexistsl_tac [`j5`, `tot`] >> simp[]) >>
  `gas_path_ptr D 0 ctx func PG Gm tm sm 0
    (set_prov Gh [ep] (FLOOKUP Gh bp))
    (th with t_var := th.t_var |+ (ep,{}))
    (OK (update_var ep (w + (32w + n2w k * n2w stride)) sh
      with vs_inst_idx := SUC sh.vs_inst_idx))` by
    (qpat_assum `gas_path_ptr _ _ _ _ _ Gm tm sm _ _ _ _` mp_tac >>
     disch_then (mp_then Any mp_tac gas_path_ptr_then) >>
     disch_then drule >> simp[]) >>
  qpat_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _` mp_tac >>
  disch_then (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >>
  simp[Abbr `sh`, Abbr `th`, Abbr `sm`, Abbr `tm`, Abbr `Gm`, update_var_def]
QED

Theorem for_dynarray_address_ready_ptr:
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes tot /\
  not_local_ptr cenv es.scopes ep /\
  (!z. cenv.ce_return_buf <> SOME (PtrVar (Var ov) z) /\
    cenv.ce_return_buf <> SOME (PtrVar (Var tot) z) /\
    cenv.ce_return_buf <> SOME (PtrVar (Var ep) z)) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst j4 ADD [Lit 32w; Var ov] [tot]) /\
  get_instruction bb (SUC (SUC s.vs_inst_idx)) =
    SOME (mk_inst j5 ADD [Var bp; Var tot] [ep]) /\
  lookup_var idx s = SOME (n2w k) /\ lookup_var bp s = SOME w /\
  ptr_covers G tn bp s (32+(k+1)*stride) /\
  w2n w + 32 + k*stride < dimword (:256) /\
  op_taint tn (Var idx) = {} /\ bp <> ov /\ bp <> tot /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  sA = ((update_var ep (w + (32w + n2w k * n2w stride))
      (update_var tot (32w + n2w k * n2w stride)
        (update_var ov (n2w k * n2w stride) s)))
      with vs_inst_idx := SUC (SUC (SUC s.vs_inst_idx))) /\
  GA = set_prov (DRESTRICT (DRESTRICT G (COMPL {ov})) (COMPL {tot}))
      [ep] (FLOOKUP G bp) /\
  tA = (tn with t_var := ((tn.t_var |+ (ov,{})) |+ (tot,{})) |+ (ep,{})) ==>
  gas_path_ptr D 0 ctx func PG G tn s 0 GA tA (OK sA) /\
  stmt_state_rel ctx func cenv cx es sA /\ ghost_inv d cenv cx es GA tA sA /\
  ptr_covers GA tA ep sA stride /\
  lookup_var ep sA = SOME (w + (32w + n2w k * n2w stride)) /\
  sA.vs_memory = s.vs_memory /\ tA.t_mem = tn.t_mem /\
  (!x. x <> ov /\ x <> tot /\ x <> ep ==>
    lookup_var x sA = lookup_var x s /\ FLOOKUP GA x = FLOOKUP G x /\
    op_taint tA (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `op_taint tn (Var bp) = {}` by fs[ptr_covers_def] >>
  conj_tac
  >- (drule_all for_dynarray_address_path_ptr >> gvs[]) >>
  conj_tac
  >- (gvs[] >> simp[stmt_state_rel_inst_idx] >>
      irule stmt_state_rel_update_var >> simp[] >>
      irule stmt_state_rel_update_var >> simp[] >>
      irule stmt_state_rel_update_var >> simp[]) >>
  conj_tac
  >- (`ghost_inv d cenv cx es (DRESTRICT G (COMPL {ov}))
        (tn with t_var := tn.t_var |+ (ov,{}))
        (update_var ov (n2w k * n2w stride) s)` by
        (irule for_scalar_overwrite_ghost >> simp[]) >>
      gvs[] >> irule (SRULE [] (Q.INST
        [`ov` |-> `tot`, `G` |-> `DRESTRICT G (COMPL {ov})`,
         `tn` |-> `tn with t_var := tn.t_var |+ (ov,{})`]
        for_element_address_outer_ghost)) >> simp[]) >>
  `w2n (w + (32w + n2w k * n2w stride)) = w2n w + 32 + k*stride` by
    (`k*stride < dimword (:256) /\ 32+k*stride < dimword (:256)` by decide_tac >>
     pure_rewrite_tac[wordsTheory.word_mul_n2w, wordsTheory.word_add_n2w] >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w]) >>
  gvs[ptr_covers_def, lookup_var_def, update_var_def, set_prov_def,
    FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def,
    arithmeticTheory.LEFT_ADD_DISTRIB] >> decide_tac
QED

Theorem for_dynarray_entry_copy_checked:
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocMemory F et et sa = ((),sb0) /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes tot /\
  not_local_ptr cenv es.scopes ep /\ not_local_ptr cenv es.scopes p /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) \/
    cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst j4 ADD [Lit 32w; Var ov] [tot]) /\
  get_instruction bb (SUC (SUC s.vs_inst_idx)) =
    SOME (mk_inst j5 ADD [Var bp; Var tot] [ep]) /\
  lookup_var idx s = SOME (n2w k) /\ lookup_var bp s = SOME w /\
  lookup_var p s = SOME dst /\
  ptr_covers G tn bp s (32+(k+1)*stride) /\ ptr_covers G tn p s sz /\
  w2n w + 32 + k*stride < dimword (:256) /\
  op_taint tn (Var idx) = {} /\ bp <> ov /\ bp <> tot /\
  p <> ov /\ p <> tot /\ p <> ep /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  stride = type_memory_size tv /\ type_memory_bytes cenv et = stride /\
  stride < dimword (:256) /\ stride <= sz /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n w + 32 + k*stride) m) /\
  not_fresh_at sa ep /\ not_fresh_at sa p /\
  fn_inst_ids_distinct func /\ MEM ainst (fn_insts func) /\
  ainst.inst_outputs = [p] /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
  local_ptrs_reserved bc sa /\ cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) ==>
  ?GA tA sA gf tf sf.
    sA = ((update_var ep (w + (32w + n2w k * n2w stride))
      (update_var tot (32w + n2w k * n2w stride)
        (update_var ov (n2w k * n2w stride) s)))
      with vs_inst_idx := SUC (SUC (SUC s.vs_inst_idx))) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 GA tA (OK sA) /\
    inst_seq_ptr D 0 ctx func PG GA tA (emitted_insts sa sb0) sA gf tf /\
    run_inst_seq (emitted_insts sa sb0) sA = OK sf /\
    ghost_inv d bc cx (es with scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes)
      gf tf sf /\
    (!x. not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep ==>
      lookup_var x sf = lookup_var x s /\ FLOOKUP gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qabbrev_tac `sA = (update_var ep (w + (32w + n2w k * n2w stride))
    (update_var tot (32w + n2w k * n2w stride)
      (update_var ov (n2w k * n2w stride) s)))
    with vs_inst_idx := SUC (SUC (SUC s.vs_inst_idx))` >>
  qabbrev_tac `GA = set_prov (DRESTRICT (DRESTRICT G (COMPL {ov})) (COMPL {tot}))
    [ep] (FLOOKUP G bp)` >>
  qabbrev_tac `tA = tn with t_var := ((tn.t_var |+ (ov,{})) |+ (tot,{})) |+ (ep,{})` >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 GA tA (OK sA) /\
   stmt_state_rel ctx func cenv cx es sA /\ ghost_inv d cenv cx es GA tA sA /\
   ptr_covers GA tA ep sA stride /\
   lookup_var ep sA = SOME (w + (32w + n2w k * n2w stride)) /\
   sA.vs_memory = s.vs_memory /\ tA.t_mem = tn.t_mem /\
   (!x. x <> ov /\ x <> tot /\ x <> ep ==>
     lookup_var x sA = lookup_var x s /\ FLOOKUP GA x = FLOOKUP G x /\
     op_taint tA (Var x) = op_taint tn (Var x))` by
    (irule for_dynarray_address_ready_ptr >>
     simp[Abbr `sA`, Abbr `GA`, Abbr `tA`] >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`bp`, `idx`, `j3`, `j4`, `j5`] >> fs[]) >>
  `ptr_covers GA tA p sA sz` by
    (`lookup_var p sA = lookup_var p s /\ FLOOKUP GA p = FLOOKUP G p /\
      op_taint tA (Var p) = op_taint tn (Var p)` by metis_tac[] >>
     drule_all for_ptr_covers_transport >> simp[]) >>
  `lookup_var p sA = SOME dst` by metis_tac[] >>
  `FLOOKUP sA.vs_allocas ainst.inst_id = SOME (w2n dst,sz)` by
    simp[Abbr `sA`, update_var_def] >>
  `!m. mem_agree_outside tA.t_mem sA.vs_memory m ==>
    val_in_memory tv v (w2n (w + (32w + n2w k * n2w stride))) m` by
    (`k*stride < dimword (:256) /\ 32+k*stride < dimword (:256)` by decide_tac >>
     gvs[] >>
     pure_rewrite_tac[wordsTheory.word_mul_n2w, wordsTheory.word_add_n2w] >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w]) >>
  `!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) \/
    cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x` by metis_tac[] >>
  `type_memory_size tv < dimword (:256) /\ type_memory_size tv <= sz /\
   type_memory_bytes cenv et = type_memory_size tv /\
   ptr_covers GA tA ep sA (type_memory_size tv)` by gvs[] >>
  drule_all for_array_element_install_checked >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`GA`, `tA`, `sA`, `gf`, `tf`, `sf`] >> simp[] >> metis_tac[]
QED

Theorem for_dynarray_copy_path_ptr:
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocMemory F et et sa = ((),sb0) /\
  sb0.cs_current_insts =
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [Lit 32w; Var ov] [tot];
     mk_inst j5 ADD [Var bp; Var tot] [ep]] ++ emitted_insts sa sb0 /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  sA = ((update_var ep (w + (32w + n2w k * n2w stride))
      (update_var tot (32w + n2w k * n2w stride)
        (update_var ov (n2w k * n2w stride) s)))
      with vs_inst_idx := 3) /\
  inst_seq_ptr D 0 ctx func PG GA tA (emitted_insts sa sb0) sA gf tf /\
  run_inst_seq (emitted_insts sa sb0) sA = OK sf ==>
  gas_path_ptr D 0 ctx func PG GA tA sA 0 gf tf
    (OK (sf with vs_inst_idx := LENGTH sb0.cs_current_insts))
Proof
  strip_tac >> drule for_array_element_copy_straight >> strip_tac >>
  `~sA.vs_halted /\ lookup_block sA.vs_current_bb func.fn_blocks = SOME bb /\
   sA.vs_inst_idx = 3` by simp[update_var_def] >>
  `isPREFIX (emitted_insts sa sb0) (DROP sA.vs_inst_idx bb.bb_instructions)` by
    (`?tail. bb.bb_instructions = sb0.cs_current_insts ++ tail` by
       metis_tac[rich_listTheory.IS_PREFIX_APPEND] >> simp[] >>
     metis_tac[rich_listTheory.IS_PREFIX_APPEND]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb0) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb0) = []` by
    (fs[listTheory.EVERY_MEM, listTheory.FILTER_EQ_NIL] >> metis_tac[]) >>
  `sA.vs_inst_idx + LENGTH (emitted_insts sa sb0) = LENGTH sb0.cs_current_insts`
    by simp[] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Theorem for_dynarray_copy_run_join:
  lookup_var idx s = SOME (n2w k) /\ lookup_var bp s = SOME w /\
  bp <> ov /\ bp <> tot /\ ov <> tot /\
  code = [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [Lit 32w; Var ov] [tot];
     mk_inst j5 ADD [Var bp; Var tot] [ep]] ++ copy /\
  EVERY (\i. ~is_terminator i.inst_opcode) copy /\
  sA = ((update_var ep (w + (32w + n2w k * n2w stride))
      (update_var tot (32w + n2w k * n2w stride)
        (update_var ov (n2w k * n2w stride) s)))
      with vs_inst_idx := n) /\
  run_inst_seq copy sA = OK sf ==>
  run_inst_seq code s = OK (sf with vs_inst_idx := s.vs_inst_idx)
Proof
  strip_tac >>
  qabbrev_tac `u = update_var ep (w + (32w + n2w k * n2w stride))
    (update_var tot (32w + n2w k * n2w stride)
      (update_var ov (n2w k * n2w stride) s))` >>
  `run_inst_seq [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [Lit 32w; Var ov] [tot];
     mk_inst j5 ADD [Var bp; Var tot] [ep]] s = OK u` by
    (drule_all (SRULE [eval_operand_def] (Q.SPEC `Var bp` (Q.GEN `saved_base`
       (SPEC_ALL dynarray_address_prefix_run)))) >>
     disch_then (qspecl_then [`stride`, `j5`, `j4`, `j3`, `ep`] mp_tac) >>
     simp[Abbr `u`, GSYM wordsTheory.word_add_n2w, GSYM wordsTheory.word_mul_n2w,
       wordsTheory.n2w_w2n, wordsTheory.WORD_ADD_ASSOC]) >>
  `run_inst_seq copy u = OK (sf with vs_inst_idx := s.vs_inst_idx)` by
    (drule run_inst_seq_inst_idx >>
     disch_then (qspecl_then [`sA`, `s.vs_inst_idx`] mp_tac) >>
     simp[instIdxIndepTheory.exec_result_map_def, Abbr `u`, update_var_def] >>
     gvs[Abbr `sA`, Abbr `u`, update_var_def]) >>
  qpat_assum `run_inst_seq [_;_;_] s = OK u`
    (mp_then Any (qspec_then `copy` mp_tac) run_inst_seq_append) >> simp[]
QED

Theorem for_dynarray_round_entry_ptr:
  dynarray_for_code func cenv bc ty stmts id et tv stride (Var bp)
    p sz ainst idx dv ov tot ep nv lv cond exit bod incr
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj /\
  for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
    bod st s0 G0 tn0 d name snapshot k es G tn s /\
  k < LENGTH vs /\ evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type tv (EL k vs) /\ val_wf tv (EL k vs) /\
  ptr_covers G tn bp s (32+(k+1)*stride) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv (EL k vs) (w2n arr_base + 32 + k*stride) m) /\
  w2n arr_base + 32 + k*stride < dimword (:256) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\ ~ctx_has_dalloca ctx /\
  lookup_block bod func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) \/
    cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  lookup_var lv s = SOME (n2w (LENGTH vs)) /\
  FLOOKUP G lv = NONE /\ op_taint tn (Var lv) = {} /\
  not_fresh_at sa lv /\ lv <> ov /\ lv <> tot /\ lv <> ep ==>
  ?gf tf s2.
    gas_path_ptr D 0 ctx func PG G tn s 0 gf tf (OK s2) /\
    stmt_state_rel ctx func bc cx
      (es with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes) s2 /\
    ghost_inv d bc cx
      (es with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes) gf tf s2 /\
    ~s2.vs_halted /\ s2.vs_current_bb = bod /\
    s2.vs_inst_idx = LENGTH sb0.cs_current_insts /\ s2.vs_allocas = s.vs_allocas /\
    ptr_covers gf tf p s2 sz /\
    FLOOKUP s2.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
    lookup_var lv s2 = SOME (n2w (LENGTH vs)) /\
    FLOOKUP gf lv = NONE /\ op_taint tf (Var lv) = {} /\
    (!x. not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep ==>
      lookup_var x s2 = lookup_var x s /\ FLOOKUP gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  drule dynarray_for_code_entry_inputs >> strip_tac >>
  `cenv_top_ext cenv bc (FEMPTY :: es.scopes)` by
    (irule dynarray_for_code_scope_frame >> goal_assum (drule_at Any) >>
     fs[for_array_inv_ptr_def, array_loop_inv_def]) >>
  qhdtm_assum `for_array_inv_ptr`
    (strip_assume_tac o PURE_REWRITE_RULE [for_array_inv_ptr_def, array_loop_inv_def]) >>
  `lookup_var bp s = SOME arr_base` by fs[eval_operand_def] >>
  `not_fresh_at sa p` by metis_tac[array_copy_live_ptrs_reserved] >>
  `not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes tot /\
   not_local_ptr cenv es.scopes ep` by metis_tac[] >>
  `stride < dimword (:256)` by decide_tac >>
  `get_instruction bb s.vs_inst_idx =
      SOME (mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]) /\
   get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst j4 ADD [Lit 32w; Var ov] [tot]) /\
   get_instruction bb (SUC (SUC s.vs_inst_idx)) =
      SOME (mk_inst j5 ADD [Var bp; Var tot] [ep])` by
    (`?tail. bb.bb_instructions = sb0.cs_current_insts ++ tail` by
       metis_tac[rich_listTheory.IS_PREFIX_APPEND] >>
     simp[get_instruction_def]) >>
  `not_local_ptr cenv es.scopes p` by
    (qpat_assum `cenv_top_ext cenv bc _` mp_tac >>
     qpat_assum `not_local_ptr bc _ p` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[not_local_ptr_def, cenv_top_ext_def, vyperStateTheory.lookup_scopes_def] >>
     strip_tac >> strip_tac >>
     conj_tac
     >- (rpt strip_tac >>
         `FLOOKUP bc.ce_vars name = FLOOKUP cenv.ce_vars name` by
           (spose_not_then assume_tac >>
            first_x_assum (qspec_then `name` mp_tac) >> simp[]) >>
         metis_tac[]) >>
     qpat_x_assum `_ = cenv`
       (mp_tac o AP_TERM ``\ce. ce.ce_imm_alloca``) >> simp[] >> metis_tac[]) >>
  `bp <> ov /\ bp <> tot` by metis_tac[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by metis_tac[] >>
  drule_all for_dynarray_entry_copy_checked >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "join"
QED

Resume for_dynarray_round_entry_ptr[join]:
  `val_in_memory tv (EL k vs) (w2n arr_base + 32 + k*stride) s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  drule_all dynarray_for_body_entry_run >>
  disch_then (qspecl_then [`j3`, `j4`, `j5`] strip_assume_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb0)` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule_all for_dynarray_copy_run_join >> strip_tac >>
  `sA = (update_var ep (arr_base + (32w + n2w k * n2w stride))
    (update_var tot (32w + n2w k * n2w stride)
      (update_var ov (n2w k * n2w stride) s))) with vs_inst_idx := 3` by (qpat_assum `sA = _` mp_tac >> simp[]) >>
  drule_all for_dynarray_copy_path_ptr >>
  disch_then assume_tac >>
  `t = sf with vs_inst_idx := s.vs_inst_idx` by
    gvs[] >>
  qpat_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
    (mp_then Any mp_tac gas_path_ptr_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qexistsl_tac [`gf`, `tf`, `sf with vs_inst_idx := LENGTH sb0.cs_current_insts`] >>
  simp[] >>
  conj_tac >- metis_tac[stmt_state_rel_inst_idx] >>
  conj_tac >- simp[ghost_inv_inst_idx] >>
  `sf.vs_halted = s.vs_halted /\ sf.vs_current_bb = s.vs_current_bb /\
   sf.vs_allocas = s.vs_allocas` by
    (qpat_assum `(t with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  simp[lookup_var_def] >>
  conj_tac
  >- metis_tac[for_ptr_covers_transport] >>
  metis_tac[lookup_var_def]
QED
Finalise for_dynarray_round_entry_ptr
