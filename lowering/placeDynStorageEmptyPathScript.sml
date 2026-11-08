Theory placeDynStorageEmptyPath
Ancestors
  placeDynStoragePath placeDynExecutionLayout placeCopyControlPath
  list rich_list arithmetic words venomState venomInst fragGasMode
  stmtSimStoreCopy fragGasSeqAbort

Theorem place_dyn_storage_empty_path:
  compile_dynarray_to_storage src dst ew ems transient sa = ((),sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s0 = SOME b /\ eval_operand dst s0 = SOME k /\
  mload (w2n b) s0 = 0w /\
  ~s0.vs_call_ctx.cc_static /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s0 0 (OK t) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0) /\
      store_copy_normalize s0 t =
        (if transient then tstore else sstore) k 0w s0 /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all place_dyn_execution_layout >> strip_tac >>
  `?r. gas_marked_path F ctx func s0 0 (OK r) /\
       store_copy_normalize s0 r = s0 /\
       (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s0) /\
       eval_operand (Var ctr) r = SOME 0w /\
       eval_operand (Var lv) r = SOME 0w /\
       ~r.vs_halted /\ r.vs_current_bb = cond /\ r.vs_inst_idx = 0`
    by suspend "init" >>
  `?u. gas_marked_path F ctx func r 0 (OK u) /\
       store_copy_normalize s0 u = s0 /\
       (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s0) /\
       eval_operand (Var lv) u = SOME 0w /\
       ~u.vs_halted /\ u.vs_current_bb = exit /\ u.vs_inst_idx = 0`
    by suspend "header" >>
  `?t. gas_marked_path F ctx func u 0 (OK t) /\
       (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0) /\
       store_copy_normalize s0 t =
         (if transient then tstore else sstore) k 0w s0 /\
       ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts`
    by suspend "finish" >>
  qexists_tac `t` >> simp[] >>
  `gas_marked_path F ctx func r 0 (OK t)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  qpat_assum `gas_marked_path _ _ _ s0 0 (OK r)`
    (mp_then Any mp_tac gas_marked_path_then) >>
  disch_then drule >> simp[]
QED

Resume place_dyn_storage_empty_path[init]:
  `lv <> ctr /\
   (!x. not_fresh_at sa x ==> x <> lv /\ x <> ctr)` by
    (fs[ALL_DISTINCT] >> metis_tac[]) >>
  `lookup_block s0.vs_current_bb func.fn_blocks = SOME bb0` by simp[] >>
  `isPREFIX [mk_inst sa.cs_next_id MLOAD [src] [lv];
            mk_inst (sa.cs_next_id+1) ASSIGN [Lit 0w] [ctr]]
      (DROP s0.vs_inst_idx bb0.bb_instructions)` by
    (qpat_assum `isPREFIX (mk_inst sa.cs_next_id MLOAD _ _::_) _`
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >> simp[]) >>
  drule_all place_dyn_init_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `get_instruction bb0 t.vs_inst_idx =
    SOME (mk_inst (sa.cs_next_id+2) JMP [Label cond] [])` by
    (qpat_assum `isPREFIX [mk_inst sa.cs_next_id MLOAD _ _;_;_] _`
       (mp_then Any strip_assume_tac instruction_prefix_cursor) >>
     qpat_assum `isPREFIX (mk_inst (sa.cs_next_id+1) ASSIGN _ _::_) _`
       (mp_then Any strip_assume_tac instruction_prefix_cursor) >>
     qpat_assum `isPREFIX [mk_inst (sa.cs_next_id+2) JMP _ _] _`
       (mp_then Any mp_tac instruction_prefix_cursor) >> simp[ADD1]) >>
  `gas_marked_path F ctx func t 0 (OK (jump_to cond t))` by
    (irule place_copy_jump_path >> simp[] >> metis_tac[]) >>
  qexists_tac `jump_to cond t` >>
  conj_tac >- (drule_all gas_marked_path_then >> simp[]) >>
  simp[jump_to_def, lookup_var_def, eval_operand_def, store_copy_normalize_def] >>
  gvs[eval_operand_def, lookup_var_def, store_copy_normalize_def]
QED

Resume place_dyn_storage_empty_path[header]:
  `lookup_block r.vs_current_bb func.fn_blocks = SOME bbh /\
   isPREFIX [mk_inst ih LT [Var ctr;Var lv] [tv];
     mk_inst (ih+1) ISZERO [Var tv] [dv];
     mk_inst (ih+2) JNZ [Var dv;Label exit;Label body_lbl] []]
     (DROP r.vs_inst_idx bbh.bb_instructions)` by simp[Excl "isPREFIX"] >>
  `tv <> dv /\ (!x. not_fresh_at sa x ==> x <> tv /\ x <> dv)` by
    (fs[ALL_DISTINCT] >> metis_tac[]) >>
  drule_at (Pat `isPREFIX _ (DROP _ _)`)
    (place_dyn_header_path |> SPEC_ALL |> Q.INST [`j` |-> `0`, `n` |-> `0`]
      |> GEN_ALL) >>
  simp[Excl "isPREFIX"] >>
  disch_then (qspecl_then [`sa`, `func`, `ctx`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  conj_tac >-
    (qpat_x_assum `store_copy_normalize r t = r`
       (mp_tac o Q.AP_TERM `store_copy_normalize s0`) >>
     simp[store_copy_normalize_def]) >>
  fs[ALL_DISTINCT, eval_operand_def] >> metis_tac[]
QED

Resume place_dyn_storage_empty_path[finish]:
  `eval_operand dst u = SOME k` by
    (`u.vs_labels = s0.vs_labels` by
       (qpat_assum `store_copy_normalize s0 u = _`
          (mp_tac o Q.AP_TERM `\s. s.vs_labels`) >>
        simp_tac (srw_ss()) [store_copy_normalize_def]) >>
     Cases_on `dst` >> simp[eval_operand_def] >>
     fs[eval_operand_def, Excl "isPREFIX"] >> metis_tac[]) >>
  `~u.vs_call_ctx.cc_static` by
    (qpat_assum `store_copy_normalize s0 u = _`
       (mp_tac o Q.AP_TERM `\s. s.vs_call_ctx`) >>
     simp_tac (srw_ss()) [store_copy_normalize_def] >> simp[]) >>
  `lookup_block u.vs_current_bb func.fn_blocks = SOME bbx /\
   isPREFIX [mk_inst ix (if transient then TSTORE else SSTORE) [dst;Var lv] []]
     (DROP u.vs_inst_idx bbx.bb_instructions)` by simp[Excl "isPREFIX"] >>
  drule_all place_dyn_length_store_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED
Finalise place_dyn_storage_empty_path
