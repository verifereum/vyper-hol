(* The nullary custom-error branch has only the four-byte selector. *)
Theory bodyCustomErrorNullaryMods
Ancestors
  bodyFullCustomErrorExit bodyFullCustomErrorLayout bodyFullExtCallBufferSetup
  bodyCustomErrorWindowBounds vyperInterpreter vyperState vyperABI vyperAST
  gasOutcomeFull fragExec venomState list pair words arithmetic
Theorem custom_error_nullary_buffer_mods:
  (?u G0 t0.
    u.vs_returndata = read_memory (w2n w+28) 4 s /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort Revert_abort u,G0,t0)) /\
  args = [] /\
  FST (eval_exprs cx [] est) = INL vs /\
  vs = [] /\ params = [] /\
  build_custom_error_data (get_tenv cx) name (MAP SND params) vs = SOME selector /\
  build_custom_error_data (get_tenv cx) name (MAP SND params) [] = SOME selector /\
  emit_op ADD [Var root;Lit 28w] a = (offset,b) /\
  fn_has_code a b func /\
  emit_inst REVERT [offset;Lit 4w] [] b = ((),en) /\
  fn_has_code b en func /\
  lookup_var root s = SOME w /\
  ptr_covers G tn root s 32 /\
  read_memory (w2n w+28) 4 s = selector /\
  w2n w + 32 <= s.vs_alloca_next /\
  s.vs_alloca_next < dimword (:256) /\
  allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  vs = [] /\ params = [] /\
  build_custom_error_data (get_tenv cx) name (MAP SND params) [] = SOME selector /\
  ?t Gf tf.
    t.vs_returndata = read_memory (w2n w+28) 4 s /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort Revert_abort t,Gf,tf)
Proof
  rpt strip_tac >>
  rpt conj_tac
  >- (first_assum ACCEPT_TAC)
  >- (first_assum ACCEPT_TAC)
  >- (first_assum ACCEPT_TAC)
  >- (qexistsl_tac [`u`,`G0`,`t0`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
QED
