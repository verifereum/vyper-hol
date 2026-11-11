Theory externalReturnWindowDispatch
Ancestors
  externalReturnZeroComplex externalReturnZeroContract abiEncoderWindowRun
  abiEncoderWindowContract abiEncoderWindow abiEncoderAdmissible abiEncoderProps
  exprLoweringProps fragExec compileEnv venomState venomInst venomMemDefs
  contractABI valueEncoding words list finite_map pred_set

Theorem return_window_run:
  !dst src ei st out st' ctx func initial at av sb source_cap d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_admissible ei /\
    abi_encoder_window_input ei at av sb source_cap initial.vs_memory /\
    eval_operand src initial = SOME (n2w sb) /\
    eval_operand dst initial = SOME (n2w d) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    alloca_inv initial /\ alloca_room ctx func initial /\
    (0 < source_cap ==>
      sb + source_cap <= initial.vs_alloca_next /\
      venomMemDefs$regions_disjoint (sb,source_cap) (d,LENGTH (enc at av))) /\
    d + LENGTH (enc at av) <= initial.vs_alloca_next /\
    (!inst b sz.
      MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids st st' /\
      FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\
      (0 < source_cap ==> venomMemDefs$regions_disjoint (sb,source_cap) (b,sz)) /\
      venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz)) /\
    ~initial.vs_halted /\
    initial.vs_current_bb = st.cs_current_bb /\
    initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?actual. abi_encoder_window_result ctx func st st' out at av d initial actual
Proof
  rpt gen_tac >> strip_tac >> Cases_on `source_cap = 0`
  >- (irule zero_window_run >> goal_assum (drule_at Any) >>
      simp_tac bool_ss [zero_window_pre_def] >> qexists_tac `sb` >>
      (* Rewrite with the assumptions only; gvs[] here took 4.7 s. *)
      qpat_x_assum `source_cap = 0` SUBST_ALL_TAC >> asm_rewrite_tac[] >>
      metis_tac[]) >>
  `0 < source_cap` by decide_tac >>
  simp_tac bool_ss [abi_encoder_window_result_def] >>
  irule compile_abi_encode_to_buf_window_run >> asm_rewrite_tac[] >>
  qexistsl_tac [`dst`, `ei`, `sb`, `source_cap`, `src`] >>
  simp[] >> metis_tac[]
QED
