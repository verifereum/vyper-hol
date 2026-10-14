(* Frozen original five-function equation claim. This is NOT regenerated from
   the current context equations. Its negation does not use those equations.
   Source: /tmp/m1-definition-hyp-audit/.typed-equations.txt, TASK064 audit. *)
Theory typedCopyCounterexample
Ancestors
  context compileEnv emitHelper vyperAST finite_map list pair
Libs
  monadsyntax

val () = monadsyntax.enable_monad "compilation";
val () = monadsyntax.enable_monadsyntax ();

Definition typed_eqs_def:
  typed_eqs <=>
  (!src_ty src dst_ty dst cenv.
   compile_store_memory_typed cenv dst dst_ty src src_ty =
    if is_word_type dst_ty then
      do val_op <- emit_op MLOAD [src]; emit_void MSTORE [dst; val_op] od
    else if is_bytestring_type dst_ty /\ is_bytestring_type src_ty then
      compile_store_bytestring src dst
    else case (dst_ty,src_ty) of
      (ArrayT dst_elem (Dynamic dst_cap), ArrayT src_elem (Dynamic _)) =>
        compile_copy_dynarray_typed cenv dst dst_elem dst_cap src src_elem
    | (ArrayT dst_elem (Fixed n), ArrayT src_elem (Fixed _)) =>
        compile_copy_sarray_typed cenv dst dst_elem src src_elem n
    | (TupleT dst_tys, TupleT src_tys) =>
        compile_typed_copy_fields cenv dst src dst_tys src_tys 0 0
    | (StructT dst_nsid, StructT src_nsid) =>
        let dst_fields = get_struct_fields cenv.ce_struct_fields (nsid_to_string dst_nsid);
            src_fields = get_struct_fields cenv.ce_struct_fields (nsid_to_string src_nsid)
        in compile_struct_typed_copy cenv dst src dst_fields src_fields 0 0
    | _ => compile_copy_memory dst src (type_memory_bytes cenv dst_ty)) /\
  (!src_tys src_off src dst_off dst cenv.
   compile_typed_copy_fields cenv dst src [] src_tys dst_off src_off = comp_return ()) /\
  (!src_off src dst_ty dst_rest dst_off dst cenv.
   compile_typed_copy_fields cenv dst src (dst_ty::dst_rest) [] dst_off src_off = comp_return ()) /\
  (!src_ty src_rest src_off src dst_ty dst_rest dst_off dst cenv.
   compile_typed_copy_fields cenv dst src (dst_ty::dst_rest) (src_ty::src_rest) dst_off src_off =
     do dst_ptr <- compile_with_byte_offset dst dst_off;
        src_ptr <- compile_with_byte_offset src src_off;
        let dst_sz = type_memory_bytes cenv dst_ty;
            src_sz = type_memory_bytes cenv src_ty
        in do compile_store_memory_typed cenv dst_ptr dst_ty src_ptr src_ty;
              compile_typed_copy_fields cenv dst src dst_rest src_rest
                (dst_off + dst_sz) (src_off + src_sz) od od) /\
  (!src_elem_ty src dst_elem_ty dst count cenv.
   compile_copy_sarray_typed cenv dst dst_elem_ty src src_elem_ty count =
    let dst_elem_sz = type_memory_bytes cenv dst_elem_ty;
        src_elem_sz = type_memory_bytes cenv src_elem_ty
    in if dst_elem_sz = src_elem_sz /\ ~is_abi_dynamic cenv.ce_struct_fields dst_elem_ty then
      compile_copy_memory dst src (count * dst_elem_sz)
    else do cond_lbl <- fresh_label "typed_sa_cond";
      body_lbl <- fresh_label "typed_sa_body"; exit_lbl <- fresh_label "typed_sa_exit";
      counter <- fresh_var; emit_inst ASSIGN [Lit 0w] [counter];
      emit_inst JMP [Label cond_lbl] []; new_block cond_lbl;
      lt_op <- emit_op LT [Var counter; Lit (n2w count)]; done_op <- emit_op ISZERO [lt_op];
      emit_inst JNZ [done_op; Label exit_lbl; Label body_lbl] []; new_block body_lbl;
      src_off <- emit_op MUL [Var counter; Lit (n2w src_elem_sz)];
      dst_off <- emit_op MUL [Var counter; Lit (n2w dst_elem_sz)];
      src_elem <- emit_op ADD [src; src_off]; dst_elem <- emit_op ADD [dst; dst_off];
      compile_store_memory_typed cenv dst_elem dst_elem_ty src_elem src_elem_ty;
      new_ctr <- emit_op ADD [Var counter; Lit 1w]; emit_inst ASSIGN [new_ctr] [counter];
      emit_inst JMP [Label cond_lbl] []; _ <- new_block exit_lbl; comp_return () od) /\
  (!src_elem_ty src dst_elem_ty dst_capacity dst cenv.
   compile_copy_dynarray_typed cenv dst dst_elem_ty dst_capacity src src_elem_ty =
    let dst_elem_sz = type_memory_bytes cenv dst_elem_ty;
        src_elem_sz = type_memory_bytes cenv src_elem_ty
    in do length <- emit_op MLOAD [src];
      too_long <- emit_op GT [length; Lit (n2w dst_capacity)]; ok <- emit_op ISZERO [too_long];
      emit_void ASSERT [ok]; emit_void MSTORE [dst; length];
      src_data <- emit_op ADD [src; Lit 32w]; dst_data <- emit_op ADD [dst; Lit 32w];
      if dst_elem_sz = src_elem_sz /\ dst_elem_ty = src_elem_ty then
        do data_sz <- emit_op MUL [length; Lit (n2w dst_elem_sz)];
           compile_copy_memory_dynamic dst_data src_data data_sz od
      else do cond_lbl <- fresh_label "typed_dyn_cond";
        body_lbl <- fresh_label "typed_dyn_body"; exit_lbl <- fresh_label "typed_dyn_exit";
        counter <- fresh_var; emit_inst ASSIGN [Lit 0w] [counter];
        emit_inst JMP [Label cond_lbl] []; new_block cond_lbl;
        lt_op <- emit_op LT [Var counter; length]; done_op <- emit_op ISZERO [lt_op];
        emit_inst JNZ [done_op; Label exit_lbl; Label body_lbl] []; new_block body_lbl;
        src_off <- emit_op MUL [Var counter; Lit (n2w src_elem_sz)];
        dst_off <- emit_op MUL [Var counter; Lit (n2w dst_elem_sz)];
        src_elem <- emit_op ADD [src_data; src_off]; dst_elem <- emit_op ADD [dst_data; dst_off];
        compile_store_memory_typed cenv dst_elem dst_elem_ty src_elem src_elem_ty;
        new_ctr <- emit_op ADD [Var counter; Lit 1w]; emit_inst ASSIGN [new_ctr] [counter];
        emit_inst JMP [Label cond_lbl] []; _ <- new_block exit_lbl; comp_return () od od) /\
  (!src_off src_fields src dst_off dst cenv.
   compile_struct_typed_copy cenv dst src [] src_fields dst_off src_off = comp_return ()) /\
  (!src_off src_fields src name dst_sz dst_rest dst_off dst_fty dst cenv.
   compile_struct_typed_copy cenv dst src ((name,dst_fty,dst_sz)::dst_rest) src_fields dst_off src_off =
    let (src_fty,src_sz) = case ALOOKUP src_fields name of
          SOME (ft,sz) => (ft,sz) | NONE => (dst_fty,dst_sz)
    in do dst_ptr <- compile_with_byte_offset dst dst_off;
          src_ptr <- compile_with_byte_offset src src_off;
          compile_store_memory_typed cenv dst_ptr dst_fty src_ptr src_fty;
          compile_struct_typed_copy cenv dst src dst_rest src_fields
            (dst_off + dst_sz) (src_off + src_sz) od)
End

(* These declarations enable only ordinary state-monad parsing. *)

Definition cycle_type_def:
  cycle_type = StructT (NONE,"AuditCycle")
End
Definition cycle_fields_def:
  cycle_fields = [("self",cycle_type,0); ("word",BaseT (UintT 256),0)]
End
Definition cycle_env_def:
  cycle_env = (ARB:compile_env) with ce_struct_fields :=
    FEMPTY |+ ("AuditCycle",cycle_fields)
End

Theorem typed_equations_not_unconditionally_true:
  ~typed_eqs
Proof
  (rewrite_tac[typed_eqs_def] >> strip_tac >>
    `compile_store_memory_typed cycle_env (Lit 0w) cycle_type
       (Lit 0w) cycle_type =
     compile_struct_typed_copy cycle_env (Lit 0w) (Lit 0w)
       cycle_fields cycle_fields 0 0` by
      (qpat_assum `!src_ty src dst_ty dst cenv. compile_store_memory_typed _ _ _ _ _ = _`
        (qspecl_then [`cycle_type`,`Lit 0w`,`cycle_type`,`Lit 0w`,`cycle_env`] mp_tac) >>
       simp_tac (srw_ss()) [cycle_type_def,cycle_env_def,get_struct_fields_def,
            is_word_type_def,is_bytestring_type_def,nsid_to_string_def,FLOOKUP_UPDATE,LET_THM]) >>
    `!st. compile_struct_typed_copy cycle_env (Lit 0w) (Lit 0w)
        cycle_fields cycle_fields 0 0 st =
      comp_bind
        (compile_store_memory_typed cycle_env (Lit 0w) cycle_type (Lit 0w) cycle_type)
        (\u. compile_store_memory_typed cycle_env (Lit 0w)
                (BaseT (UintT 256)) (Lit 0w) (BaseT (UintT 256))) st` by
      (gen_tac >> simp_tac (srw_ss()) [cycle_fields_def] >>
       qpat_assum `!src_off src_fields src name dst_sz dst_rest dst_off dst_fty dst cenv. compile_struct_typed_copy _ _ _ _ _ _ _ = _`
         (qspecl_then [`0`,`cycle_fields`,`Lit 0w`,`"self"`,`0`,
          `[("word",BaseT (UintT 256),0)]`,`0`,`cycle_type`,`Lit 0w`,`cycle_env`] mp_tac) >>
       simp_tac (srw_ss()) [cycle_fields_def,compile_with_byte_offset_def,
            comp_bind_def,comp_ignore_bind_def,comp_return_def,LET_THM,pairTheory.pair_case_thm] >>
       DISCH_THEN SUBST1_TAC >>
       qpat_assum `!src_off src_fields src name dst_sz dst_rest dst_off dst_fty dst cenv. compile_struct_typed_copy _ _ _ _ _ _ _ = _`
         (qspecl_then [`0`,`cycle_fields`,`Lit 0w`,`"word"`,`0`,
          `[]`,`0`,`BaseT (UintT 256)`,`Lit 0w`,`cycle_env`] mp_tac) >>
       simp_tac (srw_ss()) [cycle_fields_def,compile_with_byte_offset_def,
            comp_bind_def,comp_ignore_bind_def,comp_return_def,LET_THM,pairTheory.pair_case_thm] >>
       DISCH_THEN SUBST1_TAC >>
       qpat_assum `!src_off src_fields src dst_off dst cenv. compile_struct_typed_copy _ _ _ [] _ _ _ = _`
         (qspecl_then [`0`,`cycle_fields`,`Lit 0w`,`0`,`Lit 0w`,`cycle_env`] mp_tac) >>
       simp_tac (srw_ss()) [cycle_fields_def] >> DISCH_THEN SUBST1_TAC >>
       Cases_on `compile_store_memory_typed cycle_env (Lit 0w) cycle_type (Lit 0w) cycle_type st` >>
       simp_tac (srw_ss()) [comp_bind_def,comp_ignore_bind_def,comp_return_def,LET_THM,pairTheory.pair_case_thm] >>
       rpt (pop_assum kall_tac) >> pairLib.pairarg_tac >> simp[]) >>
    `!st. (SND (compile_store_memory_typed cycle_env (Lit 0w)
          (BaseT (UintT 256)) (Lit 0w) (BaseT (UintT 256)) st)).cs_next_id =
       st.cs_next_id + 2` by
      (gen_tac >>
       qpat_assum `!src_ty src dst_ty dst cenv. compile_store_memory_typed _ _ _ _ _ = _`
        (qspecl_then [`BaseT (UintT 256)`,`Lit 0w`,`BaseT (UintT 256)`,`Lit 0w`,`cycle_env`] mp_tac) >>
       simp_tac (srw_ss()) [is_word_type_def,comp_bind_def,comp_ignore_bind_def,comp_return_def,
            emit_op_def,emit_void_def,emit_inst_def,fresh_var_def,fresh_id_def,emit_def,
            LET_THM,pairTheory.pair_case_thm] >> strip_tac >> decide_tac) >>
    qpat_x_assum `!st. (SND (compile_store_memory_typed _ _ _ _ _ st)).cs_next_id = _` mp_tac >>
    qpat_x_assum `!st. compile_struct_typed_copy _ _ _ _ _ _ _ st = _` mp_tac >>
    qpat_x_assum `compile_store_memory_typed _ _ _ _ _ = compile_struct_typed_copy _ _ _ _ _ _ _` mp_tac >>
    rpt (pop_assum kall_tac) >> rpt strip_tac >>
    qpat_x_assum `compile_store_memory_typed _ _ _ _ _ = compile_struct_typed_copy _ _ _ _ _ _ _`
      (assume_tac o SYM) >>
    Cases_on `compile_store_memory_typed cycle_env (Lit 0w) cycle_type (Lit 0w) cycle_type ARB` >>
    rename1 `compile_store_memory_typed cycle_env (Lit 0w) cycle_type (Lit 0w) cycle_type ARB = (u,final)` >>
    qpat_x_assum `!st. compile_struct_typed_copy _ _ _ _ _ _ _ st = _`
      (qspec_then `ARB` mp_tac) >>
    simp[comp_bind_def,LET_THM,pairTheory.pair_case_thm] >> strip_tac >>
    qpat_x_assum `!st. (SND (compile_store_memory_typed _ _ _ _ _ st)).cs_next_id = _`
      (qspec_then `final` mp_tac) >> gvs[] >>
    qpat_x_assum `((),final) = _` (fn th =>
      simp_tac (srw_ss()) [SYM th] >> decide_tac))
QED

