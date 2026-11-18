Theory symbolicSourceCompilerStmtFrame
Ancestors
  moduleLowering
  symbolicSourceCompilerFrame stmtLowering compileEnv
Libs symbolicSourceCompilerFrameLib

open symbolicSourceCompilerFrameLib

Theorem symbolic_frame_log_save_arg:
  (!c t v. symbolic_frame R (compile_materialize_vv c t v)) ==>
  symbolic_frame R (compile_log_save_arg cenv ty op es)
Proof
  strip_tac >> simp[compile_log_save_arg_def] >> IF_CASES_TAC >> simp[]
QED

Theorem symbolic_frame_log_eval_all:
  (!c t e. symbolic_frame R (lower_value compile_expr c t e)) /\
  (!c t v. symbolic_frame R (compile_materialize_vv c t v)) ==>
  !es cenv. symbolic_frame R (compile_log_eval_all cenv es)
Proof
  strip_tac >> Induct >> simp[compile_log_eval_all_def, comp_ignore_bind_def] >>
  rpt gen_tac >>
  rpt (BETA_TAC >> irule symbolic_frame_bind >> reverse conj_tac
       >- simp[symbolic_frame_log_save_arg] >> gen_tac) >> simp[]
QED

Theorem symbolic_frame_log_topic_ops:
  (!op b. symbolic_frame R (compile_encode_log_topic op b)) ==>
  !ops. symbolic_frame R (compile_log_topic_ops ops)
Proof
  strip_tac >> Induct >> simp[compile_log_topic_ops_def, comp_ignore_bind_def] >>
  rpt gen_tac >>
  rpt (BETA_TAC >> irule symbolic_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Theorem symbolic_frame_log_store_data:
  (!op args. symbolic_frame R (emit_op op args)) /\
  (!op args. symbolic_frame R (emit_void op args)) /\
  (!c v b t s. symbolic_frame R (compile_store_memory c v b t s)) ==>
  !ops tys cenv buf off.
    symbolic_frame R (compile_log_store_data cenv ops tys buf off)
Proof
  strip_tac >> Induct >> Cases_on `tys` >>
  simp[compile_log_store_data_def, comp_ignore_bind_def] >>
  rpt gen_tac >>
  rpt (BETA_TAC >> irule symbolic_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Theorem symbolic_frame_tuple_load_all:
  (!op args. symbolic_frame R (emit_op op args)) /\
  (!op b. symbolic_frame R (compile_load_memory op b)) ==>
  !tys cenv op off. symbolic_frame R (compile_tuple_load_all cenv op tys off)
Proof
  strip_tac >> Induct >> simp[compile_tuple_load_all_def, comp_ignore_bind_def] >>
  rpt gen_tac >>
  rpt (BETA_TAC >> irule symbolic_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Theorem symbolic_frame_stmt_option_case[simp]:
  symbolic_frame R (case x of NONE => m | SOME y => f y) =
  (case x of NONE => symbolic_frame R m | SOME y => symbolic_frame R (f y))
Proof
  Cases_on `x` >> simp[]
QED

Theorem symbolic_frame_stmt_pair_case[simp]:
  symbolic_frame R ((\(x,y). f x y) p) =
  (\(x,y). symbolic_frame R (f x y)) p
Proof
  Cases_on `p` >> simp[]
QED


val _ = augment_srw_ss [rewrites [symbolic_frame_bind, symbolic_frame_ignore_bind,
                                symbolic_frame_cond]];

Theorem symbolic_frame_get_terminated[local]:
  (!g s t. R g s t ==> block_is_terminated s = block_is_terminated t) /\
  (!b. symbolic_frame R (k b)) ==>
  symbolic_frame R (comp_bind comp_get (\s. k (block_is_terminated s)))
Proof
  simp[symbolic_frame_def, comp_get_def, comp_bind_def] >> rpt strip_tac >>
  qpat_x_assum `!g s t. R g s t ==> _` (qspecl_then [`g`,`s`,`t`] mp_tac) >>
  simp[] >> strip_tac >> fs[] >>
  qpat_x_assum `!b s g t. R g s t ==> _`
    (qspecl_then [`block_is_terminated t`,`s`,`g`,`t`] mp_tac) >>
  simp[]
QED

val get_terminated_tac =
  qpat_assum `!g s t. R g s t ==> block_is_terminated s = block_is_terminated t`
    (ho_match_mp_tac o
     MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] symbolic_frame_get_terminated))

Theorem symbolic_frame_declare_stmt_local[local]:
  (!ce id ty. symbolic_frame R (declare_local ce id ty)) ==>
  symbolic_frame R (declare_stmt_local cenv s)
Proof
  strip_tac >> Cases_on `s` >> simp[declare_stmt_local_def]
QED

Theorem symbolic_frame_mcopy_guard[simp]:
  symbolic_frame R (emit_inst INVALID [] []) /\ symbolic_frame R m ==>
  symbolic_frame R (compile_mcopy_guard cenv m)
Proof
  simp[compile_mcopy_guard_def]
QED

Theorem symbolic_frame_annassign[local]:
  (!op args. symbolic_frame R (emit_void op args)) /\
  (!c id. symbolic_frame R (emit_local_alloca c id)) /\
  (!c t e. symbolic_frame R (compile_expr c t e)) /\
  (!c v. symbolic_frame R (unwrap_value c v)) /\
  (!c dst loc v p sl t s n.
    symbolic_frame R (compile_assign_value c dst loc v p sl t s n)) ==>
  symbolic_frame R (compile_stmt cenv lctx ty (AnnAssign id vtyp e))
Proof
  strip_tac >> simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  rpt (BETA_TAC >> match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac) >>
  Cases_on `FLOOKUP cenv.ce_vars id` >> simp[] >>
  rename1 `SOME binding` >> Cases_on `binding` >> simp[]
QED

Theorem symbolic_frame_stmt_cond:
  (!g s t. R g s t ==> block_is_terminated s = block_is_terminated t) /\
  (!op args. symbolic_frame R (emit_op op args)) /\
  (!op args. symbolic_frame R (emit_void op args)) /\
  (!op args outs. symbolic_frame R (emit_inst op args outs)) /\
  (!s. symbolic_frame R (fresh_label s)) /\
  symbolic_frame R fresh_var /\
  (!s. symbolic_frame R (new_block s)) /\
  (!s. symbolic_frame R (emit_jmp_if_not_terminated s)) /\
  (!c id. symbolic_frame R (emit_local_alloca c id)) /\
  (!a b c d s. symbolic_frame R (compile_range_bound_checks a b c d s)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) /\
  (!c id t. symbolic_frame R (declare_local c id t)) /\
  (!c err. symbolic_frame R (compile_revert_with_custom_error c err)) /\
  (!c t e. symbolic_frame R (compile_expr c t e)) /\
  (!c t e. symbolic_frame R (lower_value compile_expr c t e)) /\
  (!c bt. symbolic_frame R (compile_get_target_ptr compile_expr c bt)) /\
  (!c v. symbolic_frame R (unwrap_value c v)) /\
  (!c b v. symbolic_frame R (compile_snapshot_vv c b v)) /\
  (!op a b t lo hi. symbolic_frame R (compile_binop op a b t lo hi)) /\
  (!c dst loc v p sl t s n.
    symbolic_frame R (compile_assign_value c dst loc v p sl t s n)) /\
  (!i b v loc. symbolic_frame R (compile_store_at_loc i b v loc)) /\
  (!c e. symbolic_frame R (compile_reason_message c e)) /\
  (!c v (t:type) n. symbolic_frame R (compile_revert_with_reason c v t n)) /\
  (!c es. symbolic_frame R (compile_log_eval_all c es)) /\
  (!ops. symbolic_frame R (compile_log_topic_ops ops)) /\
  (!c ops tys buf off. symbolic_frame R (compile_log_store_data c ops tys buf off)) /\
  (!a b i. symbolic_frame R (compile_abi_encode_to_buf a b i)) /\
  (!c. symbolic_frame R (compile_return_unlock c)) /\
  (!k t v. symbolic_frame R (compile_nonreentrant_unlock k t v)) /\
  (!c t s v rpc. symbolic_frame R (compile_internal_return_from_env c t s v rpc)) /\
  (!rv p r i n nr k t v.
    symbolic_frame R (compile_external_return rv p r i n nr k t v)) /\
  (!c b t v s. symbolic_frame R (compile_store_memory_typed c b t v s)) /\
  (!c v b t s. symbolic_frame R (compile_store_memory c v b t s)) /\
  (!c a b w n t s cap p loc.
    symbolic_frame R (compile_dynarray_append c a b w n t s cap p loc)) /\
  (!c ty stage ts op. symbolic_frame R (compile_tuple_unpack c ty stage ts op)) /\
  (!ctor i l v. symbolic_frame R (compile_ptr_load ctor i l v)) /\
  (!c a b n l slot t s.
    symbolic_frame R (compile_iter_elem_copy c a b n l slot t s)) ==>
  (!cenv lctx ty s. symbolic_frame R (compile_stmt cenv lctx ty s)) /\
  (!cenv lctx ty ss. symbolic_frame R (compile_stmts cenv lctx ty ss))
Proof
  strip_tac >>
  ho_match_mp_tac compile_stmt_ind >> rpt strip_tac >>
  simp[symbolic_frame_annassign]
  >~ [`compile_stmt _ _ _ (Assign (BaseTarget _) _)`] >- suspend "assign"
  >~ [`compile_stmt _ _ _ (AugAssign _ _ _ _)`] >- suspend "augassign"
  >~ [`compile_stmt _ _ _ (Log _ _)`] >- suspend "log"
  >~ [`compile_stmt _ _ _ (Return NONE)`] >- suspend "return_none"
  >~ [`compile_stmt _ _ _ (Return (SOME _))`] >- suspend "return_some"
  >~ [`compile_stmt _ _ _ (If _ _ _)`] >- suspend "if"
  >~ [`compile_stmt _ _ _ (For _ _ (Range _ _) _ _)`] >- suspend "range"
  >~ [`compile_stmt _ _ _ (For _ _ (Array _) _ _)`] >- suspend "iter" >>
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  rpt (BETA_TAC >> match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac) >>
  simp[] >> suspend "cons"
QED

Resume symbolic_frame_stmt_cond[assign]:
  simp[Once compile_stmt_def, comp_ignore_bind_def] >> disj2_tac >>
  rpt (BETA_TAC >> match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[]
QED

Resume symbolic_frame_stmt_cond[augassign]:
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  rpt (BETA_TAC >> match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  rpt (BETA_TAC >> match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Resume symbolic_frame_stmt_cond[log]:
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >> rename1 `SOME info` >> PairCases_on `info` >> simp[] >>
  rpt (BETA_TAC >> match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[] >>
  disj2_tac >>
  rpt (BETA_TAC >> match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Resume symbolic_frame_stmt_cond[return_none]:
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  Cases_on `cenv.ce_return_pc` >> simp[]
  >- (Cases_on `cenv.ce_ctor_exit_label` >> simp[] >>
      pairarg_tac >> simp[] >>
      match_mp_tac symbolic_frame_bind >> simp[]) >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[] >>
  rpt (BETA_TAC >> match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[] >>
  Cases_on `cenv.ce_ctor_exit_label` >> simp[] >> pairarg_tac >> simp[] >>
  match_mp_tac symbolic_frame_bind >> simp[]
QED

Resume symbolic_frame_stmt_cond[return_some]:
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC >>
  Cases_on `cenv.ce_return_pc` >> simp[]
  >- suspend "external_return" >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[] >>
  rpt (BETA_TAC >> match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[] >>
  suspend "external_return"
QED

Resume symbolic_frame_stmt_cond[external_return]:
  rpt (BETA_TAC >> match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[]
QED

Resume symbolic_frame_stmt_cond[if]:
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  rpt (BETA_TAC >> match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac) >>
  simp[] >> suspend "if_get"
QED

Resume symbolic_frame_stmt_cond[iter]:
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  rpt (BETA_TAC >> match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[] >>
  qpat_x_assum `!arr_ty isdyn count elem c ex inc. _` (assume_tac o SRULE []) >>
  irule symbolic_frame_bind >> reverse conj_tac
  >- (BasicProvers.TOP_CASE_TAC >> simp[] >> BasicProvers.TOP_CASE_TAC >> simp[]) >>
  gen_tac >> BETA_TAC >>
  rpt (BETA_TAC >> match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Resume symbolic_frame_stmt_cond[range]:
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  rpt (BETA_TAC >> match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[] >>
  qpat_x_assum `!sgn c ex inc. _` (assume_tac o SRULE []) >>
  irule symbolic_frame_bind >> reverse conj_tac
  >- (Cases_on `start_e` >> simp[] >>
      Cases_on `end_e` >> simp[] >> rpt (BasicProvers.TOP_CASE_TAC >> simp[])) >>
  gen_tac >> BETA_TAC >>
  irule symbolic_frame_bind >> reverse conj_tac
  >- (Cases_on `start_e` >> simp[] >>
      Cases_on `end_e` >> simp[] >> rpt (BasicProvers.TOP_CASE_TAC >> simp[])) >>
  gen_tac >> BETA_TAC >>
  rpt (BETA_TAC >> match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[] >>
  irule symbolic_frame_bind >> reverse conj_tac
  >- (BasicProvers.TOP_CASE_TAC >> simp[] >> BasicProvers.TOP_CASE_TAC >> simp[]) >>
  gen_tac >> BETA_TAC >>
  rpt (BETA_TAC >> match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Resume symbolic_frame_stmt_cond[cons]:
  qpat_x_assum `!cs cenv. _ ==> symbolic_frame R (compile_stmt _ _ _ _)`
    (qspec_then `ARB with cs_current_insts := []`
       (assume_tac o SRULE [block_is_terminated_def])) >>
  qpat_x_assum `!cs cenv. _ ==> symbolic_frame R (compile_stmts _ _ _ _)`
    (qspec_then `ARB with cs_current_insts := []`
       (assume_tac o SRULE [block_is_terminated_def])) >>
  get_terminated_tac >>
  gen_tac >> Cases_on `b` >> simp[symbolic_frame_declare_stmt_local]
QED
Resume symbolic_frame_stmt_cond[if_get]:
  get_terminated_tac >> gen_tac >>
  rpt (BETA_TAC >> match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac) >>
  BETA_TAC >> get_terminated_tac >> gen_tac >>
  rpt (BETA_TAC >> match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac) >>
  simp[]
QED
Finalise symbolic_frame_stmt_cond

Theorem symbolic_frame_revert_with_reason:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) /\
  (!c v. symbolic_frame R (unwrap_value c v)) ==>
  symbolic_frame R (compile_revert_with_reason cenv msg ty n)
Proof
  strip_tac >> simp[compile_revert_with_reason_def, comp_ignore_bind_def] >>
  rpt gen_tac >>
  rpt (BETA_TAC >> irule symbolic_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Theorem symbolic_frame_reason_message:
  (!c t e. symbolic_frame R (compile_expr c t e)) /\
  (!bs n. symbolic_frame R (compile_bytelike_literal bs n)) ==>
  symbolic_frame R (compile_reason_message cenv e)
Proof
  strip_tac >> Cases_on `e` >> simp[compile_reason_message_def] >>
  rename1 `Literal t l` >> Cases_on `t` >> simp[compile_reason_message_def] >>
  rename1 `BaseT b` >> Cases_on `b` >> simp[compile_reason_message_def] >>
  Cases_on `l` >> simp[compile_reason_message_def]
QED

Theorem symbolic_frame_internal_param_decls:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  !params idx. symbolic_frame R (compile_internal_param_decls params idx)
Proof
  strip_tac >> Induct >> simp[compile_internal_param_decls_def] >>
  gen_tac >> PairCases_on `h` >> gen_tac >>
  simp[compile_internal_param_decls_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac >- frame_tac >>
       gen_tac >> BETA_TAC) >> frame_tac
QED

Theorem symbolic_frame_materialize_internal_params:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  !params cenv. symbolic_frame R (materialize_internal_params cenv params)
Proof
  strip_tac >> Induct >> simp[materialize_internal_params_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  Cases_on `h1` >> simp[materialize_internal_params_def] >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >> simp[] >>
  Cases_on `x` >> simp[comp_ignore_bind_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac >- frame_tac >>
       gen_tac >> BETA_TAC) >> frame_tac
QED

Theorem symbolic_frame_emit_local_alloca:
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) ==>
  symbolic_frame R (emit_local_alloca cenv id)
Proof
  strip_tac >> simp[emit_local_alloca_def] >> rpt BasicProvers.TOP_CASE_TAC >> simp[]
QED

Theorem symbolic_frame_range_bound_checks:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R (compile_range_bound_checks a b c d s)
Proof
  strip_tac >> Cases_on `s` >> simp[compile_range_bound_checks_def, comp_ignore_bind_def] >>
  rpt gen_tac >>
  rpt (BETA_TAC >> irule symbolic_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Theorem symbolic_frame_return_unlock:
  (!k t v. symbolic_frame R (compile_nonreentrant_unlock k t v)) ==>
  symbolic_frame R (compile_return_unlock cenv)
Proof
  strip_tac >> simp[compile_return_unlock_def] >>
  pairarg_tac >> simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem symbolic_frame_store_at_loc:
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!imm dst v. symbolic_frame R (compile_imm_store_word imm dst v)) ==>
  symbolic_frame R (compile_store_at_loc imm dst v loc)
Proof
  strip_tac >> Cases_on `loc` >> simp[compile_store_at_loc_def] >>
  rename1 `SOME l` >> Cases_on `l` >> simp[compile_store_at_loc_def]
QED

Theorem symbolic_frame_load_tuple_elements[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  !tys cenv op off.
  symbolic_frame R (compile_load_tuple_elements cenv op tys off)
Proof
  strip_tac >> Induct >> simp[compile_load_tuple_elements_def]
QED

Theorem symbolic_frame_internal_return:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) /\
  (!c v b t s. symbolic_frame R (compile_store_memory c v b t s)) ==>
  symbolic_frame R (compile_internal_return cenv rv rpc n ty sty tys rb)
Proof
  strip_tac >> Cases_on `tys` >> simp[compile_internal_return_def, comp_ignore_bind_def] >>
  rpt (FIRST [CHANGED_TAC (simp[]),
    irule symbolic_frame_bind >> reverse conj_tac >- simp[] >> gen_tac,
    BasicProvers.TOP_CASE_TAC])
QED

Theorem symbolic_frame_tuple_store_all:
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!c bt. symbolic_frame R (compile_get_target_ptr compile_expr c bt)) /\
  (!i b v. symbolic_frame R (compile_imm_store_word i b v)) /\
  (!c b l v p sl t s n.
    symbolic_frame R (compile_assign_value c b l v p sl t s n)) ==>
  !tys targets vals cenv.
    symbolic_frame R (compile_tuple_store_all cenv tys targets vals)
Proof
  strip_tac >> Induct >> Cases_on `targets` >> Cases_on `vals` >>
  simp[compile_tuple_store_all_def, comp_ignore_bind_def] >> rpt gen_tac >>
  rename1 `compile_tuple_store_all env (src::srctys) (tgt::tgts) (value::values)` >>
  Cases_on `tgt` >> simp[compile_tuple_store_all_def, comp_ignore_bind_def] >>
  rpt (FIRST [CHANGED_TAC (simp[symbolic_frame_store_at_loc]),
    irule symbolic_frame_bind >> reverse conj_tac >- simp[] >> gen_tac,
    BasicProvers.TOP_CASE_TAC])
QED

Theorem symbolic_frame_iter_elem_copy:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!v b n l. symbolic_frame R (compile_slot_to_memory v b n l)) /\
  (!ctor i l v. symbolic_frame R (compile_ptr_load ctor i l v)) /\
  (!ctor i v b n k. symbolic_frame R (compile_imm_copy_to_memory ctor i v b n k)) /\
  (!a b n. symbolic_frame R (compile_copy_memory a b n)) /\
  (!c v b t s. symbolic_frame R (compile_store_memory c v b t s)) ==>
  symbolic_frame R (compile_iter_elem_copy cenv a b n loc slot ty sty)
Proof
  strip_tac >> simp[compile_iter_elem_copy_def, comp_ignore_bind_def] >>
  rpt (FIRST [CHANGED_TAC (simp[]),
    irule symbolic_frame_bind >> reverse conj_tac >- simp[] >> gen_tac,
    BasicProvers.TOP_CASE_TAC])
QED

Theorem symbolic_frame_declare_local:
  (symbolic_frame R fresh_var) ==>
  symbolic_frame R (declare_local cenv id ty)
Proof
  strip_tac >> simp[declare_local_def] >> IF_CASES_TAC >> simp[]
QED
