Theory bodyConcatReachedCopyMods
Ancestors
  bodyConcatBytesCopyMods bodyConcatFixedCopyMods
  bodyPtrBytestringBuiltinsConcatOperand bodyConcatCutsMods bodyFullPostsMods
  vyperValue vyperTyping exprLowering
Libs monadsyntax

Theorem concat_reached_copy_mods:
  (if is_bytestring_type (expr_type e) then
     arm = (do arg_len <- emit_op MLOAD [op];
               arg_data <- emit_op ADD [op;Lit 32w];
               offset_op <- emit_op MLOAD [Var ov];
               dst <- emit_op ADD [Var dv;offset_op];
               emit_void MCOPY [dst;arg_data;arg_len];
               new_offset <- emit_op ADD [offset_op;arg_len];
               emit_void MSTORE [Var ov;new_offset]
            od)
   else ?m. expr_type e = BaseT (BytesT (Fixed m)) /\
     arm = (do offset_op <- emit_op MLOAD [Var ov];
               dst <- emit_op ADD [Var dv;offset_op];
               emit_void MSTORE [dst;op];
               new_offset <- emit_op ADD [offset_op;Lit (n2w m)];
               emit_void MSTORE [Var ov;new_offset]
            od)) /\
  arm sc = ((),s2) /\
  fn_has_code sc s2 func /\ fn_inst_ids_distinct func /\
  concat_live_mods (func,cenv,lo) (dv,ov,ow,binst,oinst,B,bsz)
    (mid,sc,t,G1,tn1) bs /\
  concat_head_post_mods (DF,lo,d,ctx,func,cenv,cx) e (es,sa,s,G,tn)
    (op,sc) H (INL v) mid G1 tn1 t /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
  (!z. op = Var z ==> not_fresh_at sc z) /\
  local_ptrs_reserved cenv sc /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sc z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sc z) /\
  LENGTH bs <= P /\
  32 + P + SUM (MAP concat_payload_capacity (expr_type e::tys)) <= bsz /\
  32 + concat_data_bound P (expr_type e::tys) <= bsz ==>
  ?u G2 tn2.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G1,tn1) [] (OK u,G2,tn2)) /\
    concat_copy_effect_mods (ctx,func,cenv,cx,lo,d) (dv,ov,ow,binst,oinst,B,bsz)
      (mid,sc,t,G1,tn1) (s2,u,G2,tn2) bs (concat_payload_mods v) /\
    LENGTH (concat_payload_mods v) <= concat_payload_capacity (expr_type e)
Proof
  Cases_on `is_bytestring_type (expr_type e)` >> asm_simp_tac bool_ss [] >>
  disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  qpat_x_assum `arm = _` SUBST_ALL_TAC
  >- (`LENGTH (concat_payload_mods v) <= concat_payload_capacity (expr_type e)` by
        (qpat_assum `concat_head_post_mods _ _ _ _ _ _ _ _ _ _`
           (strip_assume_tac o simpLib.SIMP_RULE bool_ss
             [concat_head_post_mods_def,expr_post_mods_def,sumTheory.INL_11]) >>
         drule_all concat_operand_bytes_read >>
         rewrite_tac[GSYM concat_payload_mods_def] >> strip_tac >> simp[]) >>
      `32 + LENGTH bs + concat_payload_capacity (expr_type e) <= bsz` by
        (fs[] >> decide_tac) >>
      drule_all concat_bytes_copy_cut_mods >>
      disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
      qexistsl_tac [`u`,`G'`,`tn'`] >> simp[]) >>
  `LENGTH (concat_payload_mods v) <= concat_payload_capacity (expr_type e)` by
    (Cases_on `m <= 32` >> gvs[evaluate_type_def] >> Cases_on `v` >>
     gvs[value_has_type_def,concat_payload_mods_def,concat_payload_capacity_def]) >>
  qpat_assum `concat_head_post_mods _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o simpLib.SIMP_RULE bool_ss
      [concat_head_post_mods_def,sumTheory.INL_11]) >>
  drule_all concat_fixed_copy_cut_mods >>
  disch_then (qspecl_then [`explicit`,`d`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`u`,`G'`,`tn'`] >> simp[]
QED
