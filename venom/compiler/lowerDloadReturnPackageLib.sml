(* Shared textual reconstruction packages: no HOL definitions are introduced. *)
structure lowerDloadReturnPackageLib =
struct
open HolKernel boolLib bossLib
open lowerDloadSafetyAmbientTheory lowerDloadSafetyRelationTheory

val ld_probe_guard = ``\C' k bb t.
  ?z. run_block_non_phis k C' bb t = z /\
      ((?u. z = OK u) \/ (?rt u. z = IntRet rt u))``;

val ld_probe_stable = ``\lo P Sigma names fs f0 A0 A frames.
  frames <> [] /\ TL frames = fs /\
  (HD frames).lf_serial = f0.lf_serial /\ ld_global lo A frames /\
  EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) frames /\
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
    j IN P f.lf_fn.fn_name) frames /\
  (!j k. j < k /\ k < LENGTH frames ==>
    list_precedes (EL j frames).lf_fn.fn_name
                  (EL k frames).lf_fn.fn_name names) /\
  (!g. MEM g fs ==> FRANGE g.lf_H SUBSET ld_slots A fs /\
    (!a. MEM (SOME a) g.lf_Q ==> a IN ld_slots A fs)) /\
  (!a. a IN FDOM A0 /\ a IN ld_slots A0 fs ==>
    FLOOKUP A a = FLOOKUP A0 a)``;

val ld_probe_point = ``\lo P C C' vs0 stk fn fn' cs fs f0 A0 Sigma names bb t.
  ?PG G tn inst s t0 A frames N X p h.
    ld_sync lo P C vs0 stk PG G tn fn inst s t0 A frames N /\
    ^ld_probe_stable lo P Sigma names fs f0 A0 A frames /\
    fn' = ld_image (HD frames) /\
    ld_envelope (HD frames).lf_supply fn s s.vs_inst_idx X p /\
    ld_prefix C' fn' X p h t0 t /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb /\
    ld_return_cont C fn cs s``;

(* Structural point with continuation transfer from a current source state. *)
val ld_transfer_point = ``\lo P C C' vs0 stk fn fn' source fs f0 A0 Sigma names bb t.
  ?PG G tn inst s t0 A frames N X p h.
    ld_sync lo P C vs0 stk PG G tn fn inst s t0 A frames N /\
    ^ld_probe_stable lo P Sigma names fs f0 A0 A frames /\
    fn' = ld_image (HD frames) /\
    ld_envelope (HD frames).lf_supply fn s s.vs_inst_idx X p /\
    ld_prefix C' fn' X p h t0 t /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb /\
    (!cs. ld_return_cont C fn cs source ==> ld_return_cont C fn cs s)``;

val ld_probe_entry = ``\C' fn' Point q.
  !k bb tp. lookup_block q.vs_current_bb fn'.fn_blocks = SOME bb /\
    eval_phis q bb.bb_instructions = OK tp /\
    ^ld_probe_guard C' k bb
      (tp with vs_inst_idx := phi_prefix_length bb.bb_instructions) ==>
    Point bb (tp with vs_inst_idx := phi_prefix_length bb.bb_instructions)``;

val ld_probe_terminal = ``\lo P C C' vs0 stk fn cs fs f0 A0 Sigma names rt u.
  ?sf rs cs' Ar fr tnr rinst se te PG' G' Nr.
    run_blocks sf C fn cs = IntRet rs cs' /\
    ld_sync lo P C vs0 stk PG' G' tnr fn rinst se te Ar fr Nr /\
    ^ld_probe_stable lo P Sigma names fs f0 A0 Ar fr /\
    rinst.inst_opcode = RET /\
    step_inst 0 C rinst se = IntRet rs cs' /\
    step_inst 0 C' rinst te = IntRet rt u /\
    rs.iret_values = rt.iret_values /\
    rs.iret_adopt_fmp = NONE /\ rt.iret_adopt_fmp = NONE /\
    ld_memory lo Ar tnr cs' u /\ ld_nonghost tnr cs' u /\
    (!a. a IN ld_slots Ar fs ==>
      FLOOKUP (DRESTRICT Ar (ld_slots Ar fs)) a = FLOOKUP Ar a)``;

(* The experimental ambient is unchanged. Production adds coverage explicitly. *)
val ld_probe_ambient = ``\lo C C' vs0 Sigma names fn fn'.
  o1_ctx_shape C /\ o1_run_state_ok vs0 /\
  reserved_intervals_wf C.ctx_global_reserved /\ fixed_region_reserved lo C /\
  ptr_discipline lo C vs0 /\ fmp_free_ctx C /\
  mem_inv raw_mem_ok C vs0 /\ mem_inv dload_offset_ok C vs0 /\
  mem_inv dload_headroom_ok C vs0 /\ callee_first names C.ctx_functions /\
  (!f. MEM f C.ctx_functions ==>
    lookup_function f.fn_name C'.ctx_functions =
      SOME (FST (lower_dload_function_supply (Sigma f.fn_name) f))) /\
  fn' = FST (lower_dload_function_supply (Sigma fn.fn_name) fn)``;

val ld_covered_ambient = ``\lo C C' vs0 Sigma names fn fn'.
  ^ld_probe_ambient lo C C' vs0 Sigma names fn fn' /\
  (!f. MEM f C.ctx_functions ==> ir_supply_covers_fn (Sigma f.fn_name) f)``;

val ld_probe_S = ``\Ambient Point Terminal (k:num) ctx ti t z.
  !(lo:num) (P:string -> num set) (C:venom_context) (C':venom_context)
   (vs0:venom_state) (stk:call_frame list) (fn:ir_function) (fn':ir_function)
   (cs:venom_state) (fs:ld_frame list) (f0:ld_frame) (A0:ld_alloc)
   (Sigma:string -> ir_supply) (names:string list) bb.
    ctx = C' ==>
    Ambient lo C C' vs0 Sigma names fn fn' /\
    Point lo P C C' vs0 stk fn fn' cs fs f0 A0 Sigma names bb t /\
    get_instruction bb t.vs_inst_idx = SOME ti ==>
    (case z of
       OK q => if is_terminator ti.inst_opcode then
         (~q.vs_halted ==>
          ^ld_probe_entry C' fn'
            (Point lo P C C' vs0 stk fn fn' cs fs f0 A0 Sigma names) q)
       else (!j. ^ld_probe_guard C' j bb
                     (q with vs_inst_idx := SUC t.vs_inst_idx) ==>
         Point lo P C C' vs0 stk fn fn' cs fs f0 A0 Sigma names bb
           (q with vs_inst_idx := SUC t.vs_inst_idx))
     | IntRet rt u => Terminal lo P C C' vs0 stk fn cs fs f0 A0 Sigma names rt u
     | _ => T)``;

val ld_probe_E = ``\Ambient Point Terminal (k:num) ctx bb t z.
  !(lo:num) (P:string -> num set) (C:venom_context) (C':venom_context)
   (vs0:venom_state) (stk:call_frame list) (fn:ir_function) (fn':ir_function)
   (cs:venom_state) (fs:ld_frame list) (f0:ld_frame) (A0:ld_alloc)
   (Sigma:string -> ir_supply) (names:string list).
    ctx = C' ==>
    Ambient lo C C' vs0 Sigma names fn fn' /\
    Point lo P C C' vs0 stk fn fn' cs fs f0 A0 Sigma names bb t ==>
    (case z of
       OK q => ^ld_probe_entry C' fn'
         (Point lo P C C' vs0 stk fn fn' cs fs f0 A0 Sigma names) q
     | IntRet rt u => Terminal lo P C C' vs0 stk fn cs fs f0 A0 Sigma names rt u
     | _ => T)``;

val ld_probe_R = ``\Ambient Point Terminal (k:num) ctx fnT q z.
  !(lo:num) (P:string -> num set) (C:venom_context) (C':venom_context)
   (vs0:venom_state) (stk:call_frame list) (fn:ir_function) (fn':ir_function)
   (cs:venom_state) (fs:ld_frame list) (f0:ld_frame) (A0:ld_alloc)
   (Sigma:string -> ir_supply) (names:string list).
    ctx = C' ==>
    Ambient lo C C' vs0 Sigma names fn fn' /\ fnT = fn' /\
    ^ld_probe_entry C' fn'
      (Point lo P C C' vs0 stk fn fn' cs fs f0 A0 Sigma names) q ==>
    (case z of
       IntRet rt u => Terminal lo P C C' vs0 stk fn cs fs f0 A0 Sigma names rt u
     | _ => T)``;

(* The conditional induction statement, shared by concrete specializations. *)
val ld_package_induction = ``\Ambient Point Terminal.
  (!fuel ctx inst s z.
    inst.inst_opcode <> INVOKE /\ step_inst_base inst s = z /\
    ((?t. z = OK t) \/ (?ret t. z = IntRet ret t)) ==>
    ^ld_probe_S Ambient Point Terminal fuel ctx inst s z) /\
  (!fuel ctx inst s nm ops callee args cs ret cs' t.
    inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
    lookup_function nm ctx.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
    run_blocks fuel ctx callee cs = IntRet ret cs' /\
    ^ld_probe_R Ambient Point Terminal fuel ctx callee cs (IntRet ret cs') /\
    bind_outputs inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state s cs')) = SOME t ==>
    ^ld_probe_S Ambient Point Terminal fuel ctx inst s (OK t)) ==>
  (!fuel ctx inst s z. step_inst fuel ctx inst s = z /\
    ((?t. z = OK t) \/ (?ret t. z = IntRet ret t)) ==>
    ^ld_probe_S Ambient Point Terminal fuel ctx inst s z) /\
  (!fuel ctx bb s z. run_block_non_phis fuel ctx bb s = z /\
    ((?t. z = OK t) \/ (?ret t. z = IntRet ret t)) ==>
    ^ld_probe_E Ambient Point Terminal fuel ctx bb s z) /\
  (!fuel ctx fn s z. run_blocks fuel ctx fn s = z /\
    ((?t. z = OK t) \/ (?ret t. z = IntRet ret t)) ==>
    ^ld_probe_R Ambient Point Terminal fuel ctx fn s z)``;
end
