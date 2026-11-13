(* Frame constructors and cursor-only transport, not fresh-register transport. *)
Theory bodyPtrStructLitGhostFrame
Ancestors
  bodyPtrDefs compileEnv loweringStateRelDefs venomState

Theorem ghost_inv_from_parts:
  (!name entry p sz.
     lookup_scopes name es.scopes = SOME entry /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
     ptr_covers G tn p s sz /\
     !w mem. lookup_var p s = SOME w /\
             mem_agree_outside tn.t_mem s.vs_memory mem ==>
             val_in_memory entry.type entry.value (w2n w) mem) /\
  return_buf_ptr d cenv G tn s /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          op_taint tn (Var x) = {}) /\
  stor_taint_ok cx tn s ==>
  ghost_inv d cenv cx es G tn s
Proof
  rewrite_tac[ghost_inv_def] >> strip_tac >> asm_rewrite_tac[]
QED

Theorem ghost_inv_pc:
  ghost_inv d cenv cx es G tn s ==>
  ghost_inv d cenv cx es G tn
    (s with <|vs_current_bb := lbl; vs_inst_idx := idx|>)
Proof
  Cases_on `d` >-
    (simp[ghost_inv_def, return_buf_ptr_def, ptr_covers_def,
          stor_taint_ok_def, lookup_var_def] >>
     strip_tac >> asm_rewrite_tac[]) >>
  PairCases_on `x` >>
  simp[ghost_inv_def, return_buf_ptr_def, ptr_covers_def,
       stor_taint_ok_def, lookup_var_def] >>
  strip_tac >> asm_rewrite_tac[]
QED

Theorem ghost_kept_pc_reference:
  ghost_kept cenv es sa G0 tn0 s G tn ==>
  ghost_kept cenv es sa G0 tn0
    (s with <|vs_current_bb := lbl; vs_inst_idx := idx|>) G tn
Proof
  simp[ghost_kept_def, local_region_def, lookup_var_def] >>
  strip_tac >> asm_rewrite_tac[]
QED
