(*
 * Fuel bound for the decimal-digit loop of uint2str.
 *
 * TOP-LEVEL:
 *   fuel_ok_compile_uint2str
 *)

Theory fragFuelLoopUint2str
Ancestors
  fragFuel fragFuelContextBase compileEnv emitHelper context venomInst
  builtinStrings exprSimUint2Str
Libs
  fragFuelLib

(* Structural boundary for the post-allocation tail.  Its layout and
   templates are shared with the existing uint2str simulation proof. *)
Theorem uint2str_tail_structure[local]:
  cs_extends a (u2s_end a op buf n) /\
  a.cs_next_var <= (u2s_end a op buf n).cs_next_var /\
  (cs_no_phi a ==> cs_no_phi (u2s_end a op buf n))
Proof
  conj_tac
  >- (simp[cs_extends_def, u2s_end_def] >>
      simp[u2s_blocks_def]) >>
  simp[u2s_end_def, cs_no_phi_def, u2s_blocks_def,
       u2s_setup_def, u2s_check_def, u2s_cond_def, u2s_body_def,
       u2s_zero_def, u2s_final_def, u2s_inst_def, mk_inst_def,
       listTheory.EVERY_APPEND]
QED

Theorem uint2str_structure[local]:
  compile_uint2str op n sz st = (x,st') ==>
  cs_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
  (cs_no_phi st ==> cs_no_phi st')
Proof
  strip_tac >> drule compile_uint2str_layout >> strip_tac >>
  gvs[u2s_layout_def] >>
  mp_tac (Q.SPECL [`n + sz`, `{}:string set`, `{}:string set`]
    fuel_ok_compile_alloc_buffer) >>
  rewrite_tac[fuel_ok_def] >> disch_then drule >> strip_tac >>
  mp_tac (Q.INST [`buf` |-> `ba.buf_operand`] uint2str_tail_structure) >>
  strip_tac >> conj_tac
  >- metis_tac[cs_extends_trans] >>
  simp[u2s_end_def]
QED

(* Every destination in the shared templates is fresh at the allocation
   endpoint, hence outside all protected variables at the original entry. *)
Theorem uint2str_var_not_below[local]:
  N <= a.cs_next_var ==> ~var_below N (u2s_var a k)
Proof
  strip_tac >> simp[u2s_var_def, fresh_var_def] >>
  irule var_below_fresh >> simp[]
QED

(* The loop works on a fresh copy val_var of val_op, made before the loop
   (so no precondition on val_op is needed), and on a fresh counter i_var
   from 0.  Each round (cond -> body -> cond) runs straight-line code, sets
   val_var to val_var / 10 and adds 1 to i_var, leaving through final_lbl
   when val_var is 0.  The body writes only val_var, i_var and variables it
   allocates itself, so the loop variable is the one that shrinks: a 256-bit
   value reaches 0 after at most 78 divisions by 10, so i_var is at most 78
   and never wraps, and the bound is independent of the runtime state. *)
Theorem fuel_ok_compile_uint2str:
  !val_op n_digits buf_size Wv E.
    fuel_ok Wv {} E (compile_uint2str val_op n_digits buf_size)
Proof
  cheat
QED
