(* Uniform control boundaries for recursive element-to-slot stores. *)
Theory fullStoreSlotsElements
Ancestors
  fullStoreSlotsProbe typedCopyOriginPtrBase fragGasOriginPtr
  context emitHelper exprLoweringProps loweringStateRelDefs compileEnv
  venomState ptrDiscipline venomInst finite_map list arithmetic words

Theorem store_slots_elements_header_origin_ptr:
  emit_op LT [Var counter;cnt] a = (Var x,b) /\
  emit_op ISZERO [Var x] b = (Var y,c) /\
  emit_inst JNZ [Var y;Label exit;Label blabel] [] c = ((),d) /\
  lookup_var counter s = SOME (n2w k) /\
  eval_operand cnt s = SOME (n2w n) /\ k <= n /\ n < dimword(:256) /\
  FLOOKUP G counter = NONE /\ op_prov G cnt = NONE /\
  op_taint tn (Var counter) = {} /\ op_taint tn cnt = {} /\
  fn_has_code a d func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  !D explicit PG.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (jump_to (if k=n then exit else blabel)
        (update_var y (if k=n then 1w else 0w)
          (update_var x (if k<n then 1w else 0w) s))),
       DRESTRICT (DRESTRICT G (COMPL {x})) (COMPL {y}),
       tn with t_var := (tn.t_var |+ (x,{})) |+ (y,{}))
Proof
  strip_tac >> rpt gen_tac >>
  drule_all typed_copy_origin_ptr_header_branch_path >>
  disch_then (qspecl_then [`explicit`,`PG`,`D`] strip_assume_tac) >> gvs[]
QED

Theorem store_slots_elements_init_origin_ptr:
  emit_inst ASSIGN [Lit 0w] [cv] a = ((),b) /\
  emit_inst JMP [Label hdr] [] b = ((),c) /\
  emit_op LT [Var cv;cnt] h = (Var lv,h1) /\
  emit_op ISZERO [Var lv] h1 = (Var dv,h2) /\
  emit_inst JNZ [Var dv;Label exit;Label blabel] [] h2 = ((),hj) /\
  h.cs_current_bb = hdr /\ h.cs_current_insts = [] /\
  fn_has_code a c func /\ fn_has_code h hj func /\
  eval_operand cnt s = SOME (n2w n) /\ n < dimword(:256) /\
  op_prov G cnt = NONE /\ op_taint tn cnt = {} /\
  (!x. cnt = Var x ==> x <> cv) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s ==>
  !D explicit PG.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (jump_to (if n=0 then exit else blabel)
        (update_var dv (if n=0 then 1w else 0w)
          (update_var lv (if 0<n then 1w else 0w)
            (jump_to hdr (update_var cv 0w s))))),
       DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {cv})) (COMPL {lv})) (COMPL {dv}),
       tn with t_var := ((tn.t_var |+ (cv,{})) |+ (lv,{})) |+ (dv,{}))
Proof
  strip_tac >> rpt gen_tac >>
  drule_all typed_copy_origin_ptr_counter_init_path >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`,`D`] strip_assume_tac) >>
  `eval_operand cnt t = SOME (n2w n) /\ op_prov Gf cnt = NONE /\
   op_taint tnf cnt = {}` by
    (Cases_on `cnt` >> gvs[eval_operand_def, op_prov_def, op_taint_def,
       jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT]) >>
  `allocas_from lo t` by
    (gvs[allocas_from_def, jump_to_def, update_var_def] >> metis_tac[]) >>
  `t.vs_current_bb = h.cs_current_bb /\
   t.vs_inst_idx = LENGTH h.cs_current_insts` by simp[] >>
  drule_all (Q.INST [`k` |-> `0`] typed_copy_origin_ptr_header_branch_path
    |> SRULE []) >>
  disch_then (qspecl_then [`explicit`,`PG`,`D`] strip_assume_tac) >>
  gvs[] >> metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED
