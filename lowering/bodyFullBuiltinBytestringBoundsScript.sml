(* Bounds checks use scalar temporaries and preserve their caller's buffer. *)
Theory bodyFullBuiltinBytestringBounds
Ancestors
  bodyPtrBytestringBuiltinsBounds bodyFullUnwrapRun builtinBytesMemory
  instSeqPtrLo fragGasSeqPtr fragGasOriginPtr exprLoweringProps
  venomState venomInst venomExecSemantics ptrDiscipline list finite_map
  compileEnv loweringStateRelDefs

Theorem bytestring_slice_bounds_full_run:
  compile_assert_slice_bounds start len limit sa = ((),sb) /\
  fn_has_code sa sb func /\
  eval_operand start s = SOME wa /\ eval_operand len s = SOME wn /\
  eval_operand limit s = SOME wl /\
  (!op. MEM op [start;len;limit] ==>
     op_prov G op = NONE /\ op_taint tn op = {} /\
     (!x. op = Var x ==> not_fresh_at sa x)) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  ?G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
    u.vs_current_bb = sb.cs_current_bb /\
    w2n wa + w2n wn <= w2n wl /\
    u = s with vs_vars := u.vs_vars /\
    (!x. not_fresh_at sa x ==>
       lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  strip_tac >>
  qabbrev_tac `names = GENLIST (\j. STRING #"%" (toString (sa.cs_next_var+j))) 5` >>
  qabbrev_tac `G' = FOLDL (\g x. DRESTRICT g (COMPL {x})) G names` >>
  qabbrev_tac `tn' = tn with t_var := tn.t_var |++ MAP (\x. (x,{})) names` >>
  `!D. inst_seq_ptr D 0 ctx func PG G tn
     (emitted_insts sa sb) s G' tn'` by
    (gen_tac >> simp[Abbr `G'`, Abbr `tn'`] >>
     irule compile_assert_slice_bounds_ghost_sequence >>
     simp[Abbr `names`] >>
     qexistsl_tac [`start`,`limit`,`len`,`wa`,`wl`,`wn`] >>
     simp[] >> metis_tac[MEM]) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn
     (emitted_insts sa sb) s G' tn'` by
    (gen_tac >> irule inst_seq_ptr_zero_to_lo >> simp[] >>
     qexists_tac `D` >> simp[]) >>
  `(!op x. MEM op [start;len;limit] /\ op = Var x ==> not_fresh_at sa x)` by
    metis_tac[] >>
  drule_all compile_assert_slice_bounds_reserved_normal_frame >> strip_tac >>
  drule_all compile_assert_slice_bounds_code >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (drule compile_assert_slice_bounds_layout >> simp[same_blocks_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[compile_assert_slice_bounds_mem_ok] >>
  `u.vs_current_bb = sb.cs_current_bb` by
    (qpat_assum `u = s with vs_vars := u.vs_vars`
       (mp_tac o Q.AP_TERM `\st. st.vs_current_bb`) >> simp[]) >>
  qexistsl_tac [`G'`,`tn'`] >>
  conj_tac
  >- (gen_tac >> irule emitted_origin_ptr_path >> simp[] >>
      qexistsl_tac [`emitted_insts sa sb`,`sa`] >> simp[] >>
      fs[EVERY_MEM] >> metis_tac[]) >>
  asm_simp_tac bool_ss [] >>
  conj_tac
  >- (rpt strip_tac >> simp[] >>
      simp[Abbr `G'`, Abbr `tn'`] >>
      mp_tac (INST_TYPE [alpha |-> ``:num # num``] slice_bounds_ghost_frame) >>
      simp[Abbr `names`] >> metis_tac[]) >>
  simp[Abbr `tn'`]
QED
