(* Layout and composition boundaries for the allocation/unwrap prefix. *)
Theory abiEncTuplePtrMaterializeOwned
Ancestors
  abiEncTuplePtrMaterializePrefix abiEncTuplePtrMaterializeCode
  abiEncodeArgsCase loweringPosts exprLowering vyperAST exprSimProps
  loweringStateRelDefs exprPtrUnwrapCodeCopyMarked exprPtrUnwrapCodeEdges
  valueEncodingProps exprSimMemorySource exprPtrUnwrapCode exprPtrUnwrapTypedSize
  valueEncodingTyping vyperState words

Theorem materialize_lowered_physical_capacity:
  !ce e. arg_type_fits (lowered_value_type ce e) (expr_type e) ==>
    type_memory_bytes ce (lowered_value_type ce e) <=
      type_memory_bytes ce (post_value_type ce e)
Proof
  rpt strip_tac >>
  `post_value_type ce e = expr_type e \/
   post_value_type ce e = lowered_value_type ce e` by
    (Cases_on `e` >> simp[post_value_type_def] >>
     rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
     simp[post_value_type_def, expr_type_def] >> IF_CASES_TAC >> simp[]) >>
  gvs[] >> metis_tac[cj 1 abi_args_fits_memory_bytes]
QED

Theorem materialize_physical_post_start:
  expr_post ctx fn ce cx e ee sm sb s ee v op z /\
  sa.cs_next_id <= sm.cs_next_id ==>
  expr_post ctx fn ce cx e ee (sa with cs_next_var := sm.cs_next_var)
    sb s ee v op z
Proof
  rw[expr_post_def, wb_frame_def]
  >- (irule expr_val_at_start_mono >> qexists `sm` >> simp[])
  >- (irule expr_val_own_start_mono >> qexists `sm` >> simp[])
  >- (gvs[not_fresh_at_def] >> first_x_assum irule >> simp[])
  >- (qpat_x_assum `!aid off sz. _` irule >>
      conj_tac >- (first_assum ACCEPT_TAC) >> qexists `aid` >> simp[] >> decide_tac) >>
  qpat_x_assum `~expr_has_effect e ==> _` mp_tac >>
  simp[pure_frame_def] >> strip_tac >> conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!n b sz. _` irule >> qexists `n` >> simp[]) >>
  rpt strip_tac >> qpat_x_assum `!off len. _` irule >>
  rpt strip_tac >> qpat_x_assum `!inst b sz. _` irule >>
  qexists `inst` >> simp[] >> decide_tac
QED

(* Compiler and physical-layout premises for the code branch; the execution
   itself remains in materialize_code_unwrap_owned_ptr. *)
Theorem materialize_code_physical_layout:
  unwrap_value ce (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = LocCode /\ ~ce.ce_is_ctor /\
  vv_post ctx fn ce cx e es sa sm s0 ee raw (LocatedValue t p) s /\
  ~is_word_type (post_value_type ce e) /\
  arg_type_fits (lowered_value_type ce e) (expr_type e) /\
  (!ty. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ty ==>
    type_memory_bytes ce (post_value_type ce e) = type_memory_size ty /\
    type_memory_size ty < 2**64) ==>
  t = post_value_type ce e /\
  compile_ensure_in_memory p.ptr_operand LocCode (type_memory_bytes ce t)
    ((type_memory_bytes ce t+31) DIV 32) F ce.ce_imm_alloca sm = (op,sb) /\
  32*((type_memory_bytes ce t+31) DIV 32) = type_memory_bytes ce t /\
  type_memory_bytes ce t < dimword (:256) /\
  type_memory_bytes ce (lowered_value_type ce e) <= type_memory_bytes ce t /\
  ?ty v. evaluate_type (get_tenv cx) t = SOME ty /\ val_wf ty v /\
    read_result cx raw ee = (INL v,ee)
Proof
  strip_tac >> drule_all vv_post_code_source >> strip_tac >> gvs[] >>
  `?ty. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ty /\
         val_wf ty v` by
    (gvs[immutable_holds_def, read_result_def, return_def] >>
     metis_tac[value_has_type_val_wf]) >>
  `type_memory_bytes ce (post_value_type ce e) = type_memory_size ty /\
   type_memory_size ty < 2**64` by (simp[] >> metis_tac[]) >>
  `32*((type_memory_bytes ce (post_value_type ce e)+31) DIV 32) =
     type_memory_bytes ce (post_value_type ce e)` by
    metis_tac[unwrap_typed_buffer_count, type_memory_size_slots] >>
  `type_memory_bytes ce (post_value_type ce e) < dimword (:256)` by
    (gvs[dimword_def] >> decide_tac) >>
  `type_memory_bytes ce (lowered_value_type ce e) <=
     type_memory_bytes ce (post_value_type ce e)` by
    metis_tac[materialize_lowered_physical_capacity] >>
  simp[] >> qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_runtime_code_route]
QED
