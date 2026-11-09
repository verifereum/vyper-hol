(* Task-only actual Return consumer applicability probe. *)
Theory externalReturnConsumerFit
Ancestors
  externalReturnIntcallForce externalReturnIntcallStack
  externalReturnIntcallMetadata externalReturnCopyAlloc
  externalReturnSimpleSuffix externalReturnSiteProbe
  stmtLowering compileEnv exprLowering loweringPosts
  externalReturnIntcallProducer vyperAST

Definition return_consumer_suffix_def:
  return_consumer_suffix ce ty sty op =
    comp_bind
      (if ~is_word_type ty /\
          ~(is_bytestring_type ty /\ is_bytestring_type sty) /\ sty <> ty
       then comp_bind (compile_alloc_buffer (type_memory_bytes ce ty))
         (\buf. comp_bind (comp_return buf.buf_operand)
           (\ptr. comp_ignore_bind
             (compile_store_memory_typed ce ptr ty op sty)
             (comp_return ptr)))
       else comp_return op)
      (\rop.
        if ce.ce_raw_return then
          comp_ignore_bind
            (if FST ce.ce_nonreentrant then
               compile_nonreentrant_unlock (FST (SND ce.ce_nonreentrant))
                 (FST (SND (SND ce.ce_nonreentrant)))
                 (SND (SND (SND ce.ce_nonreentrant)))
             else comp_return ())
            (comp_bind (compile_alloc_buffer (type_memory_bytes ce ty))
              (\raw_buf. comp_ignore_bind
                (compile_store_memory_typed ce raw_buf.buf_operand ty rop
                  (if ~is_word_type ty /\
                      ~(is_bytestring_type ty /\ is_bytestring_type sty) /\
                      sty <> ty then ty else sty))
                (compile_external_return (SOME raw_buf.buf_operand)
                  (is_word_type ty) T ce.ce_ret_enc_info ce.ce_max_return_size F
                  (FST (SND ce.ce_nonreentrant))
                  (FST (SND (SND ce.ce_nonreentrant)))
                  (SND (SND (SND ce.ce_nonreentrant))))))
        else
          compile_external_return (SOME rop) (is_word_type ty)
            F ce.ce_ret_enc_info ce.ce_max_return_size
            (FST ce.ce_nonreentrant) (FST (SND ce.ce_nonreentrant))
            (FST (SND (SND ce.ce_nonreentrant)))
            (SND (SND (SND ce.ce_nonreentrant))))
End

Theorem return_consumer_compile:
  ce.ce_return_pc = NONE ==>
  compile_stmt ce lc ty (Return (SOME e)) =
    comp_bind (lower_value compile_expr ce ty e)
      (return_consumer_suffix ce ty (lowered_value_type ce e))
Proof
  strip_tac >> simp[Once compile_stmt_def, return_consumer_suffix_def,
    comp_bind_def, comp_return_def, FUN_EQ_THM] >>
  gen_tac >> pairarg_tac >>
  simp[comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  Cases_on `ce.ce_raw_return` >>
  simp[comp_bind_def, comp_return_def, comp_ignore_bind_def]
QED

Theorem return_consumer_compile_split:
  ce.ce_return_pc = NONE /\
  compile_stmt ce lc ty (Return (SOME e)) sa = (u,sf) ==>
  ?op sb. lower_value compile_expr ce ty e sa = (op,sb) /\
    return_consumer_suffix ce ty (lowered_value_type ce e) op sb = (u,sf)
Proof
  strip_tac >> drule return_consumer_compile >> strip_tac >>
  gvs[comp_bind_def] >> pairarg_tac >> gvs[] >> metis_tac[]
QED

Theorem return_consumer_no_normalize:
  ~ce.ce_raw_return /\
  (is_word_type ty \/
   (is_bytestring_type ty /\ is_bytestring_type sty) \/ sty = ty) ==>
  return_consumer_suffix ce ty sty op =
    compile_external_return (SOME op) (is_word_type ty)
      F ce.ce_ret_enc_info ce.ce_max_return_size
      (FST ce.ce_nonreentrant) (FST (SND ce.ce_nonreentrant))
      (FST (SND (SND ce.ce_nonreentrant)))
      (SND (SND (SND ce.ce_nonreentrant)))
Proof
  strip_tac >> simp[return_consumer_suffix_def, comp_bind_def,
    comp_return_def, FUN_EQ_THM]
QED

(* Unlike a physical-zero-size claim, this gives exactly annotation memory.
   In the located branch the producer supplies sty = expr_type e. *)
Theorem return_consumer_annotation_memory:
  expr_post ctx func ce cx e es sa sb s0 ee v op s /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  ~is_word_type (expr_type e) ==>
  ?w. stmt_state_rel ctx func ce cx ee s /\
    eval_operand op s = SOME w /\ val_in_memory tv v (w2n w) s.vs_memory /\
    expr_val_at ce cx (expr_type e) sa sb ee v op s /\ val_wf tv v
Proof
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def] >> metis_tac[]
QED

(* Located equality discharges the layout interface at the actual copy site.
   Package/typing facts are deliberately explicit; no source ownership is
   demanded when the footprint is zero. *)
Theorem return_consumer_located_normalize:
  expr_post ctx func ce cx e es se sa s0 ee v src s /\
  sty = expr_type e /\ ~is_word_type sty /\
  compile_alloc_buffer (type_memory_bytes ce dty) sa = (buf,sm) /\
  compile_store_memory_typed ce buf.buf_operand dty src sty sm = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  type_memory_size dtv < dimword (:256) /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf dtv v /\
  (!x. src = Var x ==> not_fresh_at sa x) ==>
  frag_exec ctx sa sb (\z. z = s)
    (\t. ?w. stmt_state_rel ctx func ce cx ee t /\
      eval_operand buf.buf_operand t = SOME w /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size dtv) /\
      w2n w + type_memory_size dtv < dimword (:256) /\
      val_in_memory dtv v (w2n w) t.vs_memory /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)) (\r. F)
Proof
  strip_tac >> qpat_x_assum `sty = expr_type e` SUBST_ALL_TAC >>
  drule_all return_consumer_annotation_memory >> strip_tac >>
  irule return_normalize_expr_frag >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem return_consumer_normalize_split:
  ~ce.ce_raw_return /\ ~is_word_type ty /\
  ~(is_bytestring_type ty /\ is_bytestring_type sty) /\ sty <> ty /\
  return_consumer_suffix ce ty sty op sa = (u,sf) ==>
  ?buf sm sn.
    compile_alloc_buffer (type_memory_bytes ce ty) sa = (buf,sm) /\
    compile_store_memory_typed ce buf.buf_operand ty op sty sm = ((),sn) /\
    compile_external_return (SOME buf.buf_operand) (is_word_type ty)
      F ce.ce_ret_enc_info ce.ce_max_return_size
      (FST ce.ce_nonreentrant) (FST (SND ce.ce_nonreentrant))
      (FST (SND (SND ce.ce_nonreentrant)))
      (SND (SND (SND ce.ce_nonreentrant))) sn = (u,sf)
Proof
  simp[return_consumer_suffix_def, comp_bind_def, comp_return_def,
    comp_ignore_bind_def] >>
  rpt strip_tac >> pairarg_tac >>
  gvs[comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> metis_tac[]
QED

(* A raw return of a bytestring unlocks (here a no-op), copies the value into
   a fresh temporary of the declared type, and returns from it. *)
Theorem return_consumer_raw_split:
  return_consumer_suffix ce ty sty op sa = (u,sf) /\
  ce.ce_raw_return /\ ce.ce_nonreentrant = (F,nkey,ut,iv) /\
  is_bytestring_type ty /\ is_bytestring_type sty ==>
  ?buf sm sn.
    compile_alloc_buffer (type_memory_bytes ce ty) sa = (buf,sm) /\
    compile_store_memory_typed ce buf.buf_operand ty op sty sm = ((),sn) /\
    compile_external_return (SOME buf.buf_operand) (is_word_type ty) T
      ce.ce_ret_enc_info ce.ce_max_return_size F nkey ut iv sn = (u,sf)
Proof
  simp[return_consumer_suffix_def, comp_bind_def, comp_return_def,
    comp_ignore_bind_def] >>
  rpt strip_tac >> gvs[comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem return_consumer_intcall_located_type:
  compile_expr ce ct (Call ann (IntCall fid) args drv) sa =
    (LocatedValue sty p,sm) /\ sty = ann ==>
  lowered_value_type ce (Call ann (IntCall fid) args drv) =
    expr_type (Call ann (IntCall fid) args drv)
Proof
  strip_tac >> drule return_compile_intcall_output >>
  simp[lowered_value_type_def, expr_type_def] >> metis_tac[]
QED

(* Applicability table (C1.5.3.14.8).

   The exact compilation boundary is return_consumer_compile_split, followed
   by return_consumer_no_normalize or return_consumer_normalize_split.  Let
   ann = expr_type e, phy = lowered_value_type ce e, dst = ty.

   Located IntCall: return_intcall_located_force gives expr_post at ann and
   the successful tag equality. return_consumer_intcall_located_type turns
   that into phy=ann. For a normalizing branch, the checked wrapper
   return_consumer_located_normalize consumes this very expr_post. Its
   remaining premises are exactly the package metadata, source typing/wf,
   widening, destination size bound, freshness and code premises printed in
   that theorem. No full-type source capacity or nonzero source owner is a
   residual premise: return_normalize_expr_frag already guards ownership by
   0 < val_footprint stv v (see return_normalize_actual_frag).

   Bufferless IntCall: return_intcall_stack_force gives expr_post at ann with
   op=Lit 0w. return_selected_bufferless supplies ONLY
     phy = NoneT \/ type_memory_bytes ce phy = 0.
   The following normalization premises in return_normalize_expr_frag are
   NOT yet discharged at phy:
     evaluate_type (get_tenv cx) phy = SOME stv /\
     value_has_type stv v /\ val_wf stv v /\
     val_in_memory stv v 0 s.vs_memory /\
     expr_val_at ce cx phy se sa ee v (Lit 0w) s /\
     type_widens_to (get_tenv cx) phy dst.
   The annotation post only supplies these at ann (and does not itself
   supply value_has_type). Physical-zero metadata alone supplies none of
   these semantic claims. Zero footprint is explicitly a permitted branch
   of expr_val_at_def, so a positive ownership requirement is not the gap.
   Needed next: a checked physical-zero/NoneT interpretation boundary using
   source typing and successful annotation expr_post, or a different direct
   copy boundary for that compiler branch. No such boundary is claimed here.

   Non-normalizing cases (both producers):
   * primitive dst: return_consumer_no_normalize removes the copy. Applying
     return_word_suffix_path still requires word_value v and
       eval_operand op s = SOME (val_to_w256 v).
     expr_val_rel at ann only gives typed_val_to_w256 tv v when ann is word;
     typing/encoding agreement and any unlock wrapper remain caller work.
   * bytestring dst/phy: copy is absent. return_raw_suffix_path requires
       val_in_memory dtv v (w2n p) s.vs_memory /\
       w2n p + val_footprint dtv v <= dimword (:256).
     Located annotation memory is checked above; return_site_bytes_memory
     and return_site_string_memory supply the dynamic bytes/string layout
     transport. Physical bytestring does not by itself identify ann in the
     bufferless branch. No such identification is assumed.
   * phy=dst: copy is absent. Located equality gives annotation=dst, hence
     return_site_equal_memory. In the bufferless case phy=dst still does not
     identify ann; the same physical interpretation gap remains.

   Non-raw aggregate encoding after normalization/no-copy still consumes
   the selected ABI plan and encoding-equivalent window via
   return_output_alloc_encoder_result_rel, not merely an expr_post. That
   window/resource production, optional unlock, and counted prefix/suffix
   assembly remain outside this bounded probe. The checked applications
   here certify copy-consumer fit for the located case, not the full frozen
   frame theorem or a counterexample to it. *)
