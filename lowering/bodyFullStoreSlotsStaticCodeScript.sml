(* Compiler syntax boundary for the joint slots producer. *)
Theory bodyFullStoreSlotsStaticCode
Ancestors
  exprSimAbiEncodeObliviousCode exprSimAbiGasBridge context compileEnv
  fragExec exprLoweringProps emitHelper list

Theorem store_slots_primitive_code[local]:
  !P. EVERY P [ASSIGN;ADD;MUL;EQ;SHR;MLOAD;JMP;JNZ;SSTORE;TSTORE] ==>
    (!src dst cnt tr. code_action P
      (compile_word_copy_loop_op src dst cnt LocMemory
        (if tr then LocTransient else LocStorage) F)) /\
    (!src. code_action P (compile_bytestring_word_count src)) /\
    (!src off. code_action P (compile_lit_byte_offset src off))
Proof
  gen_tac >> simp[] >> strip_tac >> rpt conj_tac
  >- (rpt gen_tac >>
      simp[compile_word_copy_loop_op_def, compile_word_copy_loop_base_def,
        word_scale_def] >>
      Cases_on `tr` >> simp[word_scale_def] >>
      rpt (FIRST [irule code_action_bind, irule code_action_ignore_bind] >>
        simp[code_action_emit_inst, code_action_emit_op, code_action_emit_void,
             code_action_return, code_action_fresh_var, code_action_fresh_label,
             code_action_new_block, code_action_ignore_bind, code_action_bind,
             compile_ptr_load_def, compile_ptr_store_def] >> rpt gen_tac) >>
      simp[code_action_ignore_bind, code_action_emit_inst,
           code_action_new_block])
  >- simp[compile_bytestring_word_count_def, code_action_bind,
           code_action_emit_op] >>
  rpt gen_tac >> simp[compile_lit_byte_offset_def] >> IF_CASES_TAC >>
  simp[code_action_return, code_action_emit_op] >>
  Cases_on `src` >> simp[code_action_return, code_action_emit_op]
QED

Theorem store_slots_code_family:
  !P. EVERY P [ASSIGN;ADD;MUL;EQ;LT;ISZERO;SHR;MLOAD;JMP;JNZ;
              SSTORE;TSTORE;INVALID] ==>
  (!cenv src dst ty tr. code_action P (compile_store_slots cenv src dst ty tr)) /\
  (!cenv src dst members mo so tr.
    code_action P (compile_store_slots_members cenv src dst members mo so tr)) /\
  (!cenv src dst elem cnt tr.
    code_action P (compile_copy_elements_to_slots cenv src dst elem cnt tr))
Proof
  gen_tac >> simp[] >> strip_tac >>
  `(!src dst cnt tr. code_action P
      (compile_word_copy_loop_op src dst cnt LocMemory
        (if tr then LocTransient else LocStorage) F)) /\
   (!src. code_action P (compile_bytestring_word_count src)) /\
   (!src off. code_action P (compile_lit_byte_offset src off))` by
    (irule store_slots_primitive_code >> simp[]) >>
  ho_match_mp_tac compile_store_slots_ind >> rpt conj_tac
  >- suspend "dispatch"
  >- simp[Once compile_store_slots_def, code_action_return]
  >- (rpt gen_tac >> strip_tac >>
      simp[Once compile_store_slots_def, code_action_bind,
           code_action_ignore_bind])
  >> suspend "elements"
QED

Resume store_slots_code_family[dispatch]:
  rpt gen_tac >> strip_tac >> simp[Once compile_store_slots_def] >>
  Cases_on `~is_abi_dynamic cenv.ce_struct_fields ty`
  >- (simp[] >> IF_CASES_TAC
      >- (Cases_on `tr` >>
          simp[code_action_bind, code_action_emit_op, code_action_emit_void]) >>
      Cases_on `tr` >>
      simp[compile_memory_to_storage_def, compile_memory_to_transient_def,
           compile_word_copy_loop_def] >>
      gvs[code_action_def, comp_ignore_bind_def, comp_bind_def,
          comp_return_def] >>
      rpt strip_tac >> pairarg_tac >> gvs[] >>
      metis_tac[COND_CLAUSES]) >>
  simp[] >> Cases_on `is_bytestring_type ty`
  >- simp[code_action_bind, code_action_ignore_bind, code_action_return] >>
  simp[] >> IF_CASES_TAC >- simp[code_action_emit_void] >>
  Cases_on `ty` >> gvs[code_action_emit_void]
  >- (rename1 `ArrayT elem bd` >> Cases_on `bd` >>
      gvs[code_action_bind, code_action_ignore_bind,
          code_action_emit_op, code_action_emit_void] >>
      Cases_on `tr` >> gvs[] >>
      rpt (FIRST [irule code_action_bind, irule code_action_ignore_bind] >>
        simp[code_action_bind, code_action_ignore_bind,
             code_action_emit_op, code_action_emit_void] >> rpt gen_tac))
QED

Resume store_slots_code_family[elements]:
  rpt gen_tac >> strip_tac >> simp[Once compile_store_slots_def] >>
  rpt (FIRST [irule code_action_bind, irule code_action_ignore_bind] >>
       simp[code_action_emit_inst, code_action_emit_op, code_action_emit_void,
            code_action_return, code_action_fresh_var, code_action_fresh_label,
            code_action_new_block] >> rpt gen_tac) >> simp[]
QED

Finalise store_slots_code_family
