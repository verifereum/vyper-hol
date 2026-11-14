Theory readonlyInvokeCopyFwdStepsMemoryData
Ancestors
  readonlyInvokeCopyFwdStepsMemory readonlyInvokeCopyFwdStepsCore
  readonlyInvokeCopyFwdRel venomExecSemantics venomState finite_map list pred_set
  internalReturnCopyFwdSim taintAgree ptrDiscipline o1LowerDloadShared
  readonlyInvokeCopyFwdMemory spillSim

Theorem ricf_cert_write_equal_bytes:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  LENGTH xs = len /\
  (!gam. gam = cur \/ MEM gam curs \/ gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      ~(a <= db+k /\ db+k < a+len) /\
      ~(a <= sb+k /\ sb+k < a+len)) ==>
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (write_memory_with_expansion a xs s) G0)
    (ricf_effective_taint fn (write_memory_with_expansion a xs s)
      (tn0 with t_mem := tn0.t_mem DIFF {i | a <= i /\ i < a+len})) fn
    sites maps targets G0
    (tn0 with t_mem := tn0.t_mem DIFF {i | a <= i /\ i < a+len}) cur curs
    (write_memory_with_expansion a xs s) (write_memory_with_expansion a xs t)
Proof
  strip_tac >>
  match_mp_tac (ricf_cert_write_memory |> Q.INST
    [`G` |-> `G`, `tn` |-> `tn`, `len` |-> `len`]) >>
  simp[] >> rpt strip_tac >>
  `~(a <= db+k /\ db+k < a+len) /\
   ~(a <= sb+k /\ sb+k < a+len)` by metis_tac[] >>
  fs[]
QED

Theorem ricf_cert_data_copy:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  MEM inst.inst_opcode [CALLDATACOPY; DLOADBYTES; CODECOPY] /\
  inst.inst_operands = [dst;src;sizeop] /\
  eval_operand dst s = SOME (n2w a) /\ eval_operand dst t = SOME (n2w a) /\
  eval_operand src s = SOME (n2w b) /\ eval_operand src t = SOME (n2w b) /\
  eval_operand sizeop s = SOME (n2w len) /\ eval_operand sizeop t = SOME (n2w len) /\
  a < dimword (:256) /\ b < dimword (:256) /\ len < dimword (:256) /\
  data = (if inst.inst_opcode = CALLDATACOPY then s.vs_call_ctx.cc_calldata
          else if inst.inst_opcode = DLOADBYTES then s.vs_data_section else s.vs_code) /\
  data = (if inst.inst_opcode = CALLDATACOPY then t.vs_call_ctx.cc_calldata
          else if inst.inst_opcode = DLOADBYTES then t.vs_data_section else t.vs_code) /\
  xs = TAKE len (DROP b data ++ REPLICATE len 0w) /\
  (!gam. gam = cur \/ MEM gam curs \/ gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      ~(a <= db+k /\ db+k < a+len) /\
      ~(a <= sb+k /\ sb+k < a+len)) ==>
  step_inst_base inst s = OK (write_memory_with_expansion a xs s) /\
  step_inst_base inst t = OK (write_memory_with_expansion a xs t) /\
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (write_memory_with_expansion a xs s) G0)
    (ricf_effective_taint fn (write_memory_with_expansion a xs s)
      (tn0 with t_mem := tn0.t_mem DIFF {i | a <= i /\ i < a+len})) fn
    sites maps targets G0
    (tn0 with t_mem := tn0.t_mem DIFF {i | a <= i /\ i < a+len}) cur curs
    (write_memory_with_expansion a xs s) (write_memory_with_expansion a xs t)
Proof
  strip_tac >>
  `LENGTH xs = len` by (simp[] >> gvs[]) >>
  reverse (rpt conj_tac)
  >- (match_mp_tac (ricf_cert_write_equal_bytes |> Q.INST
        [`G` |-> `G`, `tn` |-> `tn`, `len` |-> `len`]) >> simp[] >> gvs[]) >>
  fs[MEM] >> gvs[] >> simp[step_inst_base_opcode_eqs] >> gvs[]
QED

Theorem ricf_cert_returndatacopy:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_operands = [dst;src;sizeop] /\
  eval_operand dst s = SOME (n2w a) /\ eval_operand dst t = SOME (n2w a) /\
  eval_operand src s = SOME (n2w b) /\ eval_operand src t = SOME (n2w b) /\
  eval_operand sizeop s = SOME (n2w len) /\ eval_operand sizeop t = SOME (n2w len) /\
  a < dimword (:256) /\ b < dimword (:256) /\ len < dimword (:256) /\
  s.vs_returndata = t.vs_returndata /\ b+len <= LENGTH s.vs_returndata /\
  xs = TAKE len (DROP b s.vs_returndata) /\
  (!gam. gam = cur \/ MEM gam curs \/ gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      ~(a <= db+k /\ db+k < a+len) /\
      ~(a <= sb+k /\ sb+k < a+len)) ==>
  step_inst_base inst s = OK (write_memory_with_expansion a xs s) /\
  step_inst_base inst t = OK (write_memory_with_expansion a xs t) /\
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (write_memory_with_expansion a xs s) G0)
    (ricf_effective_taint fn (write_memory_with_expansion a xs s)
      (tn0 with t_mem := tn0.t_mem DIFF {i | a <= i /\ i < a+len})) fn
    sites maps targets G0
    (tn0 with t_mem := tn0.t_mem DIFF {i | a <= i /\ i < a+len}) cur curs
    (write_memory_with_expansion a xs s) (write_memory_with_expansion a xs t)
Proof
  strip_tac >>
  `LENGTH xs = len` by (simp[] >> gvs[]) >>
  reverse (rpt conj_tac)
  >- (match_mp_tac (ricf_cert_write_equal_bytes |> Q.INST
        [`G` |-> `G`, `tn` |-> `tn`, `len` |-> `len`]) >> simp[] >> gvs[]) >>
  simp[step_inst_base_opcode_eqs] >> gvs[]
QED

Theorem ricf_cert_extcodecopy:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  inst.inst_opcode = EXTCODECOPY /\ inst.inst_operands = [addr;dst;src;sizeop] /\
  eval_operand addr s = SOME account /\ eval_operand addr t = SOME account /\
  eval_operand dst s = SOME (n2w a) /\ eval_operand dst t = SOME (n2w a) /\
  eval_operand src s = SOME (n2w b) /\ eval_operand src t = SOME (n2w b) /\
  eval_operand sizeop s = SOME (n2w len) /\ eval_operand sizeop t = SOME (n2w len) /\
  a < dimword (:256) /\ b < dimword (:256) /\ len < dimword (:256) /\
  (lookup_account (w2w account) s.vs_accounts).code =
    (lookup_account (w2w account) t.vs_accounts).code /\
  xs = TAKE len (DROP b (lookup_account (w2w account) s.vs_accounts).code ++ REPLICATE len 0w) /\
  (!gam. gam = cur \/ MEM gam curs \/ gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      ~(a <= db+k /\ db+k < a+len) /\
      ~(a <= sb+k /\ sb+k < a+len)) ==>
  step_inst_base inst s = OK (write_memory_with_expansion a xs s) /\
  step_inst_base inst t = OK (write_memory_with_expansion a xs t) /\
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (write_memory_with_expansion a xs s) G0)
    (ricf_effective_taint fn (write_memory_with_expansion a xs s)
      (tn0 with t_mem := tn0.t_mem DIFF {i | a <= i /\ i < a+len})) fn
    sites maps targets G0
    (tn0 with t_mem := tn0.t_mem DIFF {i | a <= i /\ i < a+len}) cur curs
    (write_memory_with_expansion a xs s) (write_memory_with_expansion a xs t)
Proof
  strip_tac >>
  `LENGTH xs = len` by (simp[] >> gvs[]) >>
  reverse (rpt conj_tac)
  >- (match_mp_tac (ricf_cert_write_equal_bytes |> Q.INST
        [`G` |-> `G`, `tn` |-> `tn`, `len` |-> `len`]) >> simp[] >> gvs[]) >>
  simp[step_inst_base_opcode_eqs] >> gvs[]
QED

Theorem ricf_cross_istore:
  ircf_cross tn gam s t /\ m SUBSET count 32 /\
  (!db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
    ~(a <= db+k /\ db+k < a+32) /\ ~(a <= sb+k /\ sb+k < a+32)) ==>
  ircf_cross
    (tn with <|t_mem := (tn.t_mem DIFF {i | a <= i /\ i < a+32}) UNION
                          {a+k | k IN m};
               t_imm := key_update tn.t_imm a m|>) gam
    (istore a x s) (istore a y t)
Proof
  strip_tac >> irule ricf_cross_byte_frame >> qexistsl_tac [`s`, `t`, `tn`] >>
  simp[] >> rpt strip_tac >>
  `~(a <= db+k /\ db+k < a+32) /\
   ~(a <= sb+k /\ sb+k < a+32)` by metis_tac[arithmeticTheory.ADD_COMM] >>
  simp[istore_def, spillSimTheory.read_byte_mstore_outside] >>
  fs[SUBSET_DEF] >>
  metis_tac[arithmeticTheory.ADD_COMM, arithmeticTheory.LESS_EQ_ADD,
            arithmeticTheory.LESS_MONO_ADD_EQ]
QED

Theorem ricf_frame_istore:
  ricf_frame_agree D X sites PG G tn s t /\
  word_agree_except m x y /\ m SUBSET count 32 /\
  (!db sb sz k. (db,sb,sz) IN ricf_site_triples sites /\ k < sz ==>
    ~(a <= db+k /\ db+k < a+32) /\
    ~(a <= sb+k /\ sb+k < a+32)) ==>
  ricf_frame_agree D X sites PG G
    (tn with <|t_mem := (tn.t_mem DIFF {i | a <= i /\ i < a+32}) UNION
                          {a+k | k IN m};
               t_imm := key_update tn.t_imm a m|>)
    (istore a x s) (istore a y t)
Proof
  strip_tac >>
  `taint_agree D X
    (tn with <|t_mem := (tn.t_mem DIFF {i | a <= i /\ i < a+32}) UNION
                          {a+k | k IN m};
               t_imm := key_update tn.t_imm a m|>)
    (istore a x s)
    (istore a y (t with <|vs_vars := s.vs_vars; vs_params := s.vs_params|>))` by
    (irule taint_agree_istore >> fs[ricf_frame_agree_def]) >>
  `ircf_cross
    (tn with <|t_mem := (tn.t_mem DIFF {i | a <= i /\ i < a+32}) UNION
                          {a+k | k IN m};
               t_imm := key_update tn.t_imm a m|>)
    (ricf_site_triples sites) (istore a x s) (istore a y t)` by
    (irule ricf_cross_istore >> fs[ricf_frame_agree_def] >> metis_tac[]) >>
  fs[ricf_frame_agree_def] >>
  simp[ricf_frame_agree_def, istore_def, mstore_def, op_taint_def] >>
  gvs[istore_def, mstore_def, op_taint_def]
QED

Theorem ricf_merge_istore:
  merge_callee_state caller (istore a x s) =
  istore a x (merge_callee_state caller s)
Proof
  simp[merge_callee_state_def, istore_def, mstore_def]
QED

Theorem ricf_cert_istore:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  word_agree_except m x y /\ m SUBSET count 32 /\
  inst.inst_opcode = ISTORE /\ inst.inst_operands = [addr;value] /\
  eval_operand addr s = SOME (n2w a) /\ eval_operand addr t = SOME (n2w a) /\
  eval_operand value s = SOME x /\ eval_operand value t = SOME y /\
  a < dimword (:256) /\
  mask = (tn0 with <|t_mem := (tn0.t_mem DIFF {i | a <= i /\ i < a+32}) UNION
                          {a+k | k IN m};
                     t_imm := key_update tn0.t_imm a m|>) /\
  (!gam. gam = cur \/ MEM gam curs \/ gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      ~(a <= db+k /\ db+k < a+32) /\
      ~(a <= sb+k /\ sb+k < a+32)) ==>
  step_inst_base inst s = OK (istore a x s) /\
  step_inst_base inst t = OK (istore a y t) /\
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (istore a x s) G0)
    (ricf_effective_taint fn (istore a x s) mask) fn
    sites maps targets G0 mask cur curs (istore a x s) (istore a y t)
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs] >>
  qpat_x_assum `ricf_cert_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ricf_cert_core_def, ricf_live_boundary_core_def]) >>
  irule ricf_cert_reconstruct >>
  conj_tac >- (gvs[] >> irule ricf_cross_istore >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  conj_tac
  >- (fs[ricf_cert_crosses_def, EVERY_MEM] >>
      simp[ricf_cert_crosses_def, EVERY_MEM] >> rpt strip_tac >>
      gvs[] >> irule ricf_cross_istore >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  conj_tac
  >- (`ircf_dead ids (istore a x s) stk = ircf_dead ids s stk /\
        (istore a x s).vs_params = s.vs_params` by
        simp[ircf_dead_def, istore_def, mstore_def] >>
      asm_rewrite_tac[] >> gvs[] >> irule ricf_frame_istore >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  fs[ricf_live_stack_agree_def] >>
  simp[ricf_live_stack_agree_def, ricf_merge_istore] >> rpt strip_tac >>
  match_mp_tac (ricf_frame_istore |> Q.INST
    [`tn` |-> `tn0 with t_var := (EL j stk).cf_tvar`] |> SRULE []) >>
  simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED
