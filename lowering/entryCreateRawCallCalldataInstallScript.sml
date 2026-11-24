(* Static installation of the word-list and administrative intervals. *)
Theory entryCreateRawCallCalldataInstall
Ancestors
  entryCreateIntervalLayout createSizeOperandCode createSizeCutCode
  compilerInstructionSuffix compileExprAllocaFresh exprSimWordArgs
  createSizeCutRegion abiEncoderProps exprSimAbiGasBridge fragExec
  loweringShapeDefs venomFnInstsProofs venomExecProps venomInst
  venomExecSemantics compileEnv list rich_list

Theorem raw_call_get_instruction_mem[local]:
  get_instruction bb k = SOME i ==> MEM i bb.bb_instructions
Proof
  simp[get_instruction_def,AllCaseEqs()] >> metis_tac[EL_MEM]
QED

Theorem raw_call_calldata_word_list_code[local]:
  !args sa xs sb.
    lower_word_args ce expr_type args sa = (xs,sb) ==>
    create_cut_code {} sa sb
Proof
  Induct >> simp[lower_word_args_nil,lower_word_args_cons] >> rpt strip_tac >>
  irule create_cut_code_join >> qexists_tac `s1` >> conj_tac
  >- (qspecl_then [`ce`,`expr_type h`,`h`,`sa`] mp_tac (cj 2 create_operand_cut_code) >> simp[]) >>
  metis_tac[]
QED

(* The installed exit index follows the installed prefix in its own block.
   All other installed fragment blocks have a different label. *)
Theorem raw_call_exit_not_added[local]:
  cs_extends a b /\ fn_has_code a b fn /\ create_layout a b /\
  fn_inst_ids_distinct fn /\
  lookup_block b.cs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
  ~MEM i (added_insts a b)
Proof
  strip_tac >> strip_tac >>
  `?new. b.cs_blocks = new ++ a.cs_blocks` by fs[cs_extends_def] >>
  `emitted_blocks a b = new` by metis_tac[emitted_blocks_append] >>
  `MEM i (FLAT (MAP (\bb. bb.bb_instructions) (REVERSE new)) ++
          b.cs_current_insts)` by
    (qpat_x_assum `MEM i (added_insts a b)` mp_tac >>
     simp[added_insts_def,state_insts_def,all_blocks_def,
          REVERSE_APPEND,MAP_APPEND,FLAT_APPEND,DROP_APPEND] >>
     qmatch_goalsub_abbrev_tac `DROP (LENGTH xs + n) xs` >>
     `DROP (LENGTH xs + n) xs = []` by simp[DROP_EQ_NIL] >>
     simp[] >> metis_tac[MEM_DROP_IMP]) >>
  `MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions` by
    metis_tac[lookup_block_MEM,raw_call_get_instruction_mem] >>
  fs[MEM_APPEND,MEM_FLAT,MEM_MAP,MEM_REVERSE]
  >- (rename1 `MEM emitted new` >>
      `lookup_block emitted.bb_label fn.fn_blocks = SOME emitted` by fs[fn_has_code_def] >>
      `emitted = bb` by metis_tac[lookup_block_MEM,inst_in_unique_block] >>
      `bb.bb_label = b.cs_current_bb` by metis_tac[lookup_block_label] >>
      fs[create_layout_def,MEM_MAP] >> metis_tac[]) >>
  `?tail. bb.bb_instructions = b.cs_current_insts ++ tail` by
    fs[fn_has_code_def,IS_PREFIX_APPEND] >>
  `ALL_DISTINCT (MAP (\x. x.inst_id) bb.bb_instructions)` by
    metis_tac[fn_inst_ids_block_distinct] >>
  gvs[get_instruction_def,EL_APPEND_EQN,MAP_APPEND,ALL_DISTINCT_APPEND,AllCaseEqs()] >>
  Cases_on `tail` >> fs[MEM_MAP] >> metis_tac[]
QED

Theorem raw_call_exit_not_in_band[local]:
  create_cut_code {} a b /\ fn_has_code a b fn /\ create_layout a b /\
  fn_inst_ids_distinct fn /\
  (!id. id IN frag_ids a b ==>
        ?j. MEM j (added_insts a b) /\ j.inst_id = id) /\
  lookup_block b.cs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
  i.inst_id NOTIN frag_ids a b
Proof
  strip_tac >> strip_tac >>
  `?j. MEM j (added_insts a b) /\ j.inst_id = i.inst_id` by metis_tac[] >>
  `cs_extends a b` by fs[create_cut_code_def] >>
  `MEM j (fn_insts fn) /\ MEM i (fn_insts fn)` by
    metis_tac[added_insts_function_member,lookup_block_fn_insts,raw_call_get_instruction_mem] >>
  `j = i` by metis_tac[venomInstIdsPropsTheory.fn_inst_ids_distinct_inj] >>
  metis_tac[raw_call_exit_not_added]
QED

(* All fields refer to the same installed function and the same shared exit.
   The optional GAS interval may be empty. *)
Definition raw_call_calldata_split_def:
  raw_call_calldata_split fn a m b <=>
    create_cut_code {} a m /\ create_cut_code {} m b /\
    fn_has_code a m fn /\ fn_has_code m b fn /\
    create_layout a m /\ create_layout m b /\
    a.cs_next_id <= m.cs_next_id /\ m.cs_next_id <= b.cs_next_id /\
    (!u. create_cut_region a m u /\ ~create_operand_at m u ==>
         ~create_operand_at b u) /\
    (!bb i. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb /\
            get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
            i.inst_id NOTIN frag_ids a m)
End

Theorem raw_call_calldata_split_intro[local]:
  create_cut_code {} a m /\ create_cut_code {} m b /\
  fn_has_code a b fn /\ create_layout a b /\
  (!bb i. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
          i.inst_id NOTIN frag_ids a b) ==>
  raw_call_calldata_split fn a m b
Proof
  strip_tac >>
  `cs_extends a m /\ cs_extends m b /\
   a.cs_next_id <= m.cs_next_id /\ m.cs_next_id <= b.cs_next_id` by fs[create_cut_code_def] >>
  `fn_has_code a m fn /\ fn_has_code m b fn` by metis_tac[fn_has_code_split] >>
  `create_layout a m /\ create_layout m b` by
    metis_tac[create_layout_subinterval,cs_extends_refl] >>
  `!u. create_cut_region a m u /\ ~create_operand_at m u ==>
       ~create_operand_at b u` by metis_tac[create_layout_left_stop] >>
  simp[raw_call_calldata_split_def] >> fs[frag_ids_def] >>
  rpt strip_tac >> res_tac >> decide_tac
QED

(* The reusable emitter certificates enter at their concrete equations.
   No property of an evaluated word list, or of a later request, is used. *)
Theorem raw_call_calldata_installed_splits:
  compile_expr ce ty (Call ann (RawCallCalldataTarget flags) (a::kws) dflt) sa =
    (vv,sb) /\
  lower_word_args ce expr_type (a::kws) sa = (addr::xs,s2) /\
  (case go of SOME g => (g,s2) | NONE => emit_op GAS [] s2) = (gas,s3) /\
  compile_raw_call_outbuf flags.rcf_max_outsize s3 = ((ov,optr),s4) /\
  compile_msg_data_to_memory s4 = ((dp,len),s5) /\
  compile_raw_call_finish addr dp len gas value kind
    flags.rcf_max_outsize flags.rcf_revert_on_failure ov optr s5 = (result,sb) /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ create_layout sa sb /\
  ((case go of SOME g => (g,s2) | NONE => emit_op GAS [] s2) = (gas,s3) ==>
     create_cut_code {} s2 s3 /\
     EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code s2 s3)) /\
  (compile_raw_call_outbuf flags.rcf_max_outsize s3 = ((ov,optr),s4) ==>
     create_cut_code {} s3 s4 /\
     EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code s3 s4)) /\
  (compile_msg_data_to_memory s4 = ((dp,len),s5) ==>
     create_cut_code {} s4 s5 /\
     EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code s4 s5)) /\
  (compile_raw_call_finish addr dp len gas value kind
      flags.rcf_max_outsize flags.rcf_revert_on_failure ov optr s5 = (result,sb) ==>
     create_cut_code {} s5 sb /\
     EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code s5 sb)) ==>
  raw_call_calldata_split fn sa s2 sb /\
  raw_call_calldata_split fn s2 s3 sb /\
  raw_call_calldata_split fn s3 s4 sb /\
  raw_call_calldata_split fn s4 s5 sb /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code s2 s3) /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code s3 s4) /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code s4 s5) /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code s5 sb)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `create_cut_code {} sa s2` by metis_tac[raw_call_calldata_word_list_code] >>
  `create_cut_code {} s2 s3 /\ create_cut_code {} s3 s4 /\
   create_cut_code {} s4 s5 /\ create_cut_code {} s5 sb` by simp[] >>
  `create_cut_code {} s4 sb` by metis_tac[create_cut_code_join] >>
  `create_cut_code {} s3 sb` by metis_tac[create_cut_code_join] >>
  `create_cut_code {} s2 sb` by metis_tac[create_cut_code_join] >>
  `create_cut_code {} sa sb` by metis_tac[create_cut_code_join] >>
  `!bb i. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH sb.cs_current_insts) = SOME i ==>
          i.inst_id NOTIN frag_ids sa sb` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     irule raw_call_exit_not_in_band >>
     qpat_assum `lookup_block _ _ = SOME _` (irule_at Any) >> simp[] >>
     drule compile_expr_alloca_fresh >> simp[]) >>
  `!a'. create_cut_code {} sa a' /\ create_cut_code {} a' sb ==>
        fn_has_code a' sb fn /\ create_layout a' sb /\
        (!bb i. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
                get_instruction bb (LENGTH sb.cs_current_insts) = SOME i ==>
                i.inst_id NOTIN frag_ids a' sb)` by
    (rpt strip_tac >> fs[create_cut_code_def]
     >- metis_tac[fn_has_code_mid,cs_extends_refl]
     >- metis_tac[create_layout_subinterval,cs_extends_refl] >>
     fs[frag_ids_def] >> res_tac >> decide_tac) >>
  `create_cut_code {} sa s3 /\ create_cut_code {} sa s4` by
    metis_tac[create_cut_code_join] >>
  simp[] >> rpt conj_tac >> irule raw_call_calldata_split_intro >> simp[] >>
  metis_tac[]
QED
