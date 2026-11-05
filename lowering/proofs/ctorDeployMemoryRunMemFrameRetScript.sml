(* The constructor exit and epilogue with memory: every return from the
 * constructor body (a valueless Return, the only one it types) halts
 * memory-safely through the jump to the exit block, the unlock, and the
 * epilogue's ALLOCA, MCOPY of the immutables, CODECOPY of the runtime code
 * and RETURN.  The memory twin of constructor_frame_ret_ok, in a frame with
 * no caller return buffer.
 * TOP-LEVEL: constructor_frame_ret_ok_mem (admitted until proved).
 *)
Theory ctorDeployMemoryRunMemFrameRet
Ancestors
  ctorDeployLoweringFrameRet bodyMemoryDefs

Theorem constructor_frame_ret_ok_mem:
  !ctx func cenv cx runtime_size immutables_len imm nr nkey ut exit_lbl
   st_exit st_epilogue st_final.
    cenv.ce_is_ctor /\ cenv.ce_return_pc = NONE /\
    cenv.ce_ctor_exit_label = SOME exit_lbl /\
    st_exit.cs_current_bb = exit_lbl /\ st_exit.cs_current_insts = [] /\
    (if nr then compile_nonreentrant_unlock nkey ut F else comp_return ())
      st_exit = ((), st_epilogue) /\
    compile_constructor_epilogue runtime_size immutables_len imm
      st_epilogue = ((), st_final) /\
    fn_has_code st_exit st_final func /\
    runtime_size + immutables_len < dimword(:256) /\
    (nr ==> ut /\ storage_layout_safe cx /\
            cx.nonreentrant_slot = SOME nkey) /\
    (immutables_len <> 0 ==>
      cenv.ce_imm_alloca = SOME imm /\
      (!x. imm = Var x ==> not_fresh_at st_epilogue x)) ==>
    frame_ret_ok_mem NONE ctx func cx (\v es r. T) cenv NoneT
Proof
  cheat
QED
