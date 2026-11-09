(* Memory case of the body induction: a slice of anything but self.code
   (bodyMemBiSlice's split).  A slice of x.code evaluates start and len
   before the address x (code_slice_source), so its premises are the
   induction's code-slice ones: the tail's judgment, and the address's after
   the tail evaluates; any other slice takes its operands' judgment. *)
Theory bodyMemBiSliceNonSelf
Ancestors
  bodyMemoryPreds exprLowering bodyMemSliceScratch bodyMemSliceTypedContinue
  bodyMemSliceDynamicCapture bodyMemSliceNonselfResult
  exprSimHypsDefs exprSimSliceSource vyperContext

Theorem body_builtin_slice_nonself_mem:
  !cx ty n es.
    (!code_ty addr s3 tail_vs t'.
       builtin_args_length_ok (Slice n) (LENGTH es) /\
       code_slice_source (Slice n) es = SOME (code_ty,addr) /\
       eval_exprs cx (TL es) s3 = (INL tail_vs,t') ==>
       body_exprs_mem_ok cx [addr]) /\
    (!code_ty addr.
       builtin_args_length_ok (Slice n) (LENGTH es) /\
       code_slice_source (Slice n) es = SOME (code_ty,addr) ==>
       body_exprs_mem_ok cx (TL es)) /\
    (builtin_args_length_ok (Slice n) (LENGTH es) /\
     code_slice_source (Slice n) es = NONE ==>
     body_exprs_mem_ok cx es) /\
    ~is_self_code (HD es) ==>
    body_expr_mem_ok cx (Builtin ty (Slice n) es)
Proof
  rpt gen_tac >> strip_tac >>
  match_mp_tac body_expr_mem_ok_intro >> conj_tac >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  `builtin_args_length_ok (Slice n) (LENGTH es)` by
    (`well_typed_expr env (Builtin ty (Slice n) es)` by fs[expr_body_pre_def] >>
     drule slice_typed_args >> strip_tac >> gvs[builtin_args_length_ok_def]) >>
  `expr_vv_sim_mem ctx func cenv cx ty' (Builtin ty (Slice n) es) es'` by
    (irule slice_nonself_vv_mem >> simp[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- metis_tac[] >> metis_tac[]) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule slice_nonself_sim_mem >> simp[] >> metis_tac[]
QED
