(* Consume the same selector and payload observed at the terminal ADD. *)
Theory bodyCustomErrorTerminalMods
Ancestors
  bodyFullCustomErrorExit gasOutcomeFullPostMods fragGasOriginPtrLoop
  fragExec bodyPtrDefs exprSimDefs vyperABI vyperState vyperInterpreter
  venomExecSemantics memoryReadProps words

Theorem custom_error_terminal_outcome_mods:
  build_custom_error_data (get_tenv cx) name formals vs = SOME data /\
  ~u.vs_halted /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
         (u,Gu,tu) [] (OK s,G,tn)) /\
  read_memory (w2n w+28) (4+k) s = data /\
  emit_op ADD [Var root;Lit 28w] a = (offset,b) /\ fn_has_code a b func /\
  (case encoded of
     NONE => k = 0 /\ len = Lit 4w /\ c = b
   | SOME op => emit_op ADD [Lit 4w;op] b = (len,c) /\ fn_has_code b c func /\
                eval_operand op s = SOME (n2w k) /\ op_taint tn op = {} /\
                (!x. op = Var x ==> not_fresh_at a x)) /\
  emit_inst REVERT [offset;len] [] c = ((),en) /\ fn_has_code c en func /\
  lookup_var root s = SOME w /\ ptr_covers G tn root s (32+k) /\
  w2n w + 32+k <= s.vs_alloca_next /\ s.vs_alloca_next < dimword (:256) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind (lift_option (build_custom_error_data (get_tenv cx) name formals vs)
       "custom error encoding") (\data. raise (Error (RevertData data))))
    (mid,u,Gu,tu) Q
    (\H res ee gt r.
       (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
       halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==>
         !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  strip_tac >> drule_all custom_error_terminal_path >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`t`,`Gf`,`tf`] strip_assume_tac)) >>
  `t.vs_returndata = data` by fs[] >>
  irule gas_outcome_full_mods_exit_revert >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gf`,`mid`,`INR (Error (RevertData data))`,`tf`,`t`] >>
  simp[bind_def, lift_option_def, raise_def, return_def, exit_result_def,
       stmt_exit_ptr_def, expr_exit_def, halt_exit_def] >>
  rpt strip_tac >> irule gas_origin_ptr_path_trans >>
  qexistsl_tac [`G`,`s`,`tn`] >> simp[]
QED
