(* Semantic consumers of the checked post-CALL state. *)
Theory rawCallFinishSuffixPtr
Ancestors
  rawCallFinishBridgePtr rawCallSourceDomainPtr rawCallResultProofPtr
  wordArgsPtr wordOperandsPtr exprSimWordArgs bodyPtrDefs
  fragGasPathPtr valueEncoding exprLoweringProps loweringPosts
Libs monadsyntax

Theorem raw_call_scalar_suffix:
  return op sa = (result,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv dep cenv cx es G tn s /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ is_word_type ty /\
  type_memory_bytes cenv (lowered_value_type cenv e) = 0 /\
  eval_operand op s = SOME (val_to_w256 v) /\
  op_taint tn op = {} /\ op_prov G op = NONE ==>
  gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 G tn (OK s) /\
  ptr_val_ok cx ty v result G tn s /\ ptr_buf_ok cenv e result G s /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv dep cenv cx es G tn s /\
  ghost_kept cenv es protected G tn s G tn /\ wb_frame cenv es protected s s /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  eval_operand result s = SOME (val_to_w256 v) /\ ~s.vs_halted
Proof
  strip_tac >> gvs[compileEnvTheory.comp_return_def] >>
  simp[bodyPtrDefsTheory.ptr_val_ok_word, bodyPtrDefsTheory.ptr_buf_ok_def,
    wordArgsPtrTheory.ghost_kept_refl, exprSimWordArgsTheory.wb_frame_refl] >>
  irule (cj 1 gas_path_ptr_rules) >> simp[]
QED

Theorem raw_call_success_bytes_suffix:
  emit_inst JNZ [ok;Label good;Label bad] [] sa = ((),sj) /\
  new_block good sk = (blockname,sn) /\
  (do z <- emit_op RETURNDATASIZE [];
      cmp <- emit_op LT [z;Lit (n2w n)];
      cap <- compile_select cmp z (Lit (n2w n));
      emit_void MSTORE [Var dst;cap]; return (Var dst) od) sn = (result,sb) /\
  fn_has_code sa sj func /\ fn_has_code sn sb func /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv dep cenv cx es G tn s /\
  local_ptrs_reserved cenv protected /\ ci_mono protected sn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at protected x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at protected x) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  eval_operand ok s = SOME 1w /\ op_taint tn ok = {} /\
  LENGTH s.vs_returndata < dimword(:256) /\ n < dimword(:256) /\
  not_fresh_at sn dst /\ lookup_var dst s = SOME a /\
  ptr_covers G tn dst s capacity /\ 32 <= capacity /\
  bs = TAKE n s.vs_returndata /\
  mem_bytes_at (w2n a+32) (LENGTH bs) s.vs_memory = bs /\
  (!i. w2n a+32 <= i /\ i < w2n a+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic n))) /\
  val_store_size (BaseTV (BytesT (Dynamic n))) (BytesV bs) <= capacity /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= capacity /\
  (!name off len. local_region cenv es.scopes s name off len ==>
    regions_disjoint (w2n a) 32 off len) /\
  (!aid off len. aid < protected.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
    regions_disjoint (w2n a) 32 off len) ==>
  ?H un t. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 H un (OK t) /\
    ptr_val_ok cx ty (BytesV bs) result H un t /\ ptr_buf_ok cenv e result H t /\
    ghost_inv dep cenv cx es H un t /\ ghost_kept cenv es protected G tn s H un /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es protected s t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~t.vs_halted /\ t.vs_returndata = s.vs_returndata
Proof
  strip_tac >> drule_all raw_call_success_branch_stage >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `wb_frame cenv es protected s (jump_to good s)` by
    simp[loweringPostsTheory.wb_frame_def, loweringPostsTheory.locals_kept_def,
      venomStateTheory.jump_to_def, venomStateTheory.lookup_var_def,
      compileEnvTheory.local_region_def] >>
  `?H un t. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn (jump_to good s) 0 H un (OK t) /\
    ptr_val_ok cx ty (BytesV bs) (Var dst) H un t /\ ptr_buf_ok cenv e (Var dst) H t /\
    ghost_inv dep cenv cx es H un t /\ ghost_kept cenv es protected G tn (jump_to good s) H un /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es protected (jump_to good s) t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~t.vs_halted /\ t.vs_returndata = s.vs_returndata /\ result = Var dst` by
    (mp_tac (raw_call_bytes_suffix_stage |> Q.INST [`s` |-> `jump_to good s`, `sa` |-> `sn`]) >>
     impl_tac >- (gvs[venomStateTheory.jump_to_def, venomStateTheory.lookup_var_def,
       bodyPtrDefsTheory.ptr_covers_def, compileEnvTheory.local_region_def] >> metis_tac[]) >>
     strip_tac >>
     qexistsl_tac [`H`, `un`, `t`] >> gvs[venomStateTheory.jump_to_def]) >>
  `ci_mono protected protected` by simp[exprLoweringPropsTheory.ci_mono_refl] >>
  `ghost_kept cenv es protected G tn s H un /\ wb_frame cenv es protected s t` by
    (irule (oracle_suffix_frames_compose |> Q.INST
      [`sa` |-> `protected`, `t` |-> `jump_to good s`, `H` |-> `G`, `un` |-> `tn`]) >>
     goal_assum (drule_at Any) >> simp[wordArgsPtrTheory.ghost_kept_refl] >> metis_tac[]) >>
  qexistsl_tac [`H`, `un`, `t`] >> simp[] >>
  drule_all gas_path_ptr_then >> gvs[]
QED
