(* TOP-LEVEL: execute the first actual data field and prepare the saved
   arguments, buffer operand, memory bounds and actual cut for the tail. *)
Theory typedLogDataHead
Ancestors
  typedCopyStateFrame
  typedLogArgs typedLogArgsFrames typedLogRanges typedLogFieldApply typedLogFieldContract
  typedLogStoreCode typedStoreFrames typedCopyContract typedSArrayDynInvariant
  valueLoadProps memoryValueDefs valueEncoding abiStaticLoopCode
  context stmtLowering compileEnv fragExec fragBlockPath venomState venomInst list words arithmetic

Theorem log_store_cons_head_path:
  !ctx func cenv src aty ops fty fts ftv ftvs atv atvs buf field_offset cs ret cs' ss v vs buf_addr.
    log_field_type_contract ctx func cenv fty aty ftv atv /\
    compile_log_store_data cenv ((src,aty)::ops) (fty::fts) buf field_offset cs = (ret,cs') /\
    fn_has_code cs cs' func /\ cut_continuation_no_phi cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    log_args_rel ((src,aty)::ops) (atv::atvs) (v::vs) ss /\
    log_args_safe ((src,aty)::ops) (atv::atvs) ss
      (w2n buf_addr + field_offset) (type_memory_size (TupleTV (ftv::ftvs))) /\
    eval_operand buf ss = SOME buf_addr /\
    w2n buf_addr + field_offset + type_memory_size (TupleTV (ftv::ftvs)) < dimword(:256) /\
    EVERY (\name. buf <> Var name)
      (compiler_var_names cs.cs_next_var (cs'.cs_next_var - cs.cs_next_var)) /\
    log_args_avoid ((src,aty)::ops)
      (compiler_var_names cs.cs_next_var (cs'.cs_next_var - cs.cs_next_var)) ==>
    ?mid out.
      compile_log_store_data cenv ops fts buf (field_offset + type_memory_bytes cenv fty) mid = (ret,cs') /\
      fn_has_code mid cs' func /\ cs.cs_next_var <= mid.cs_next_var /\ mid.cs_next_var <= cs'.cs_next_var /\
      fragment_path ctx func ss out /\ copy_state_frame ss out /\ out.vs_current_bb = mid.cs_current_bb /\
      out.vs_inst_idx = LENGTH mid.cs_current_insts /\ ~out.vs_halted /\
      value_has_type ftv v /\ memory_value_rel ftv v (w2n buf_addr + field_offset) out.vs_memory /\
      array_copy_frame ftv 1 (w2n buf_addr + field_offset) ss.vs_memory out.vs_memory /\
      eval_operand buf out = SOME buf_addr /\ log_args_rel ops atvs vs out /\
      log_args_safe ops atvs out (w2n buf_addr + field_offset + type_memory_size ftv)
        (type_memory_size (TupleTV ftvs)) /\
      EVERY (\name. buf <> Var name)
        (compiler_var_names mid.cs_next_var (cs'.cs_next_var - mid.cs_next_var)) /\
      log_args_avoid ops (compiler_var_names mid.cs_next_var (cs'.cs_next_var - mid.cs_next_var)) /\
      (!arg_op. EVERY (\name. arg_op <> Var name)
        (compiler_var_names cs.cs_next_var (mid.cs_next_var - cs.cs_next_var)) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_log_store_data_cons_cuts >>
  disch_then (qx_choose_then `mid` strip_assume_tac) >>
  mp_tac (Q.SPECL [`(src,aty)::ops`, `buf`, `cs.cs_next_var`, `mid.cs_next_var`, `cs'.cs_next_var`]
    log_args_allocation_split) >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  mp_tac (Q.SPECL [`ftv`, `ftvs`, `w2n (buf_addr:bytes32) + field_offset`, `dimword(:256)`]
    log_target_cons_bounds) >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >>
  `log_args_safe ((src,aty)::ops) (atv::atvs) ss (w2n buf_addr + field_offset) (type_memory_size ftv)` by
    (mp_tac (Q.SPECL [`(src,aty)::ops`, `atv::atvs`, `ss`, `w2n (buf_addr:bytes32) + field_offset`,
       `type_memory_size (TupleTV (ftv::ftvs))`, `w2n (buf_addr:bytes32) + field_offset`, `type_memory_size ftv`]
       log_args_safe_subrange) >> impl_tac
     >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
       simp_tac (srw_ss()) [type_memory_size_def]]) >> simp[]) >>
  qpat_assum `log_args_rel _ _ _ ss` (strip_assume_tac o PURE_REWRITE_RULE [log_args_rel_def]) >>
  qpat_assum `log_args_safe _ _ ss _ (type_memory_size ftv)`
    (strip_assume_tac o PURE_REWRITE_RULE [log_args_safe_def]) >>
  `EVERY (\name. src <> Var name) (compiler_var_names cs.cs_next_var (mid.cs_next_var - cs.cs_next_var))` by
    fs[log_args_avoid_def] >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cenv`, `fty`, `aty`, `ftv`, `atv`, `src`, `buf`, `field_offset`, `cs`, `()`, `mid`,
    `ss`, `v`, `buf_addr`] log_field_type_contract_path) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> disch_then (qx_choose_then `out` strip_assume_tac) >>
  mp_tac (Q.SPECL [`(src,aty)::ops`, `atv::atvs`, `v::vs`, `ss`, `out`, `TupleTV (ftv::ftvs)`,
    `w2n (buf_addr:bytes32) + field_offset`, `ftv`, `w2n (buf_addr:bytes32) + field_offset`,
    `compiler_var_names cs.cs_next_var (mid.cs_next_var - cs.cs_next_var)`] log_args_frame_contained) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
    simp_tac (srw_ss()) [type_memory_size_def]]) >> strip_tac >>
  `eval_operand buf out = SOME buf_addr` by
    (mp_tac (Q.SPECL [`compiler_var_names cs.cs_next_var (mid.cs_next_var - cs.cs_next_var)`, `buf`, `ss`, `out`, `buf_addr`]
       compiler_operand_frame_value) >> simp[]) >>
  `log_args_safe ops atvs out (w2n buf_addr + field_offset + type_memory_size ftv) (type_memory_size (TupleTV ftvs))` by
    (mp_tac (Q.SPECL [`(src,aty)::ops`, `atv::atvs`, `out`, `w2n (buf_addr:bytes32) + field_offset`,
       `type_memory_size (TupleTV (ftv::ftvs))`, `w2n (buf_addr:bytes32) + field_offset + type_memory_size ftv`,
       `type_memory_size (TupleTV ftvs)`] log_args_safe_subrange) >>
     impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
       simp_tac (srw_ss()) [type_memory_size_def, ADD_ASSOC]]) >>
     simp[log_args_safe_def]) >>
  qpat_assum `log_args_rel ((src,aty)::ops) (atv::atvs) (v::vs) out`
    (strip_assume_tac o PURE_REWRITE_RULE [log_args_rel_def]) >>
  qpat_assum `log_args_avoid ((src,aty)::ops) (compiler_var_names mid.cs_next_var _)`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [log_args_avoid_def]) >>
  qexistsl_tac [`mid`, `out`] >> rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
    asm_simp_tac (srw_ss()) [log_args_rel_def, log_args_avoid_def] >> NO_TAC]
QED
