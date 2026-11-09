(* Producer-independent return setup. Actual internal function setup uses
   PtrVar parameters, so the literal-MLOAD obstruction is not universal. *)
Theory bodyPtrStructLitReturnBoundary
Ancestors stmtLowering moduleLowering context compileEnv bodyPtrStructLitCallExclusion

Theorem structlit_return_buffer_memloc:
  cenv.ce_return_buf = SOME (MemLoc off sz) ==>
  compile_internal_return_from_env cenv ty src_ty value rpc =
  do buf <- emit_op MLOAD [Lit (n2w off)];
     compile_internal_return cenv (SOME value) rpc cenv.ce_returns_count ty src_ty
       (case ty of TupleT tys => tys
        | StructT sid => MAP (FST o SND)
            (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
        | _ => []) (SOME buf)
  od
Proof
  strip_tac >> simp[compile_internal_return_from_env_def, FUN_EQ_THM] >>
  gen_tac >> simp[comp_bind_def, comp_return_def] >>
  Cases_on `emit_op MLOAD [Lit (n2w off)] x` >> gvs[]
QED

Theorem structlit_return_buffer_ptrvar:
  cenv.ce_return_buf = SOME (PtrVar buf sz) ==>
  compile_internal_return_from_env cenv ty src_ty value rpc =
  compile_internal_return cenv (SOME value) rpc cenv.ce_returns_count ty src_ty
    (case ty of TupleT tys => tys
     | StructT sid => MAP (FST o SND)
         (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
     | _ => []) (SOME buf)
Proof
  strip_tac >> simp[compile_internal_return_from_env_def, FUN_EQ_THM] >>
  gen_tac >> simp[comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[comp_bind_def, comp_return_def]
QED

(* This is exactly moduleLowering's cenv1 return-field update, after PARAM
   and RETPC_PARAM have supplied their operands. It bypasses both setup loads. *)
Theorem structlit_internal_return_setup_fields:
  cenv.ce_return_buf = SOME (MemLoc off sz) /\
  cenv1 = (cenv with
    <| ce_return_buf :=
         (case (SOME param, cenv.ce_return_buf) of
            (SOME op, SOME (MemLoc old len)) => SOME (PtrVar op len)
          | _ => cenv.ce_return_buf);
       ce_return_pc := SOME (PtrVar pc 0) |>) ==>
  cenv1.ce_return_buf = SOME (PtrVar param sz) /\
  cenv1.ce_return_pc = SOME (PtrVar pc 0)
Proof
  simp[] >> rpt strip_tac >> gvs[]
QED

Theorem structlit_return_stmt_ptrvars:
  cenv.ce_return_pc = SOME (PtrVar pc pcsz) /\
  cenv.ce_return_buf = SOME (PtrVar buf bufsz) ==>
  compile_stmt cenv lctx ty (Return (SOME e)) =
  do value <- lower_value compile_expr cenv ty e;
     compile_internal_return cenv (SOME value) pc cenv.ce_returns_count ty
       (lowered_value_type cenv e)
       (case ty of TupleT tys => tys
        | StructT sid => MAP (FST o SND)
            (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
        | _ => []) (SOME buf)
  od
Proof
  strip_tac >> simp[Once compile_stmt_def, FUN_EQ_THM] >>
  gen_tac >> simp[comp_bind_def] >> pairarg_tac >>
  drule structlit_return_buffer_ptrvar >> simp[]
QED
