Theory bodyPtrStructLitOwnershipTyped
Ancestors bodyPtrStructLitOwnershipLocations bodyPtrStructLitOwnershipLoops
  bodyPtrStructLitOwnershipMemory bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipSteps context compileEnv venomInst list

Theorem alloc_run_typed_copy:
  (!ce dst dt src st. alloc_run fresh_outputs
    (compile_store_memory_typed ce dst dt src st) (\u s. fresh_outputs s)) /\
  (!ce dst src dts sts doff soff. alloc_run fresh_outputs
    (compile_typed_copy_fields ce dst src dts sts doff soff)
    (\u s. fresh_outputs s)) /\
  (!ce dst dt src st n. alloc_run fresh_outputs
    (compile_copy_sarray_typed ce dst dt src st n) (\u s. fresh_outputs s)) /\
  (!ce dst dt cap src st. alloc_run fresh_outputs
    (compile_copy_dynarray_typed ce dst dt cap src st) (\u s. fresh_outputs s)) /\
  (!ce dst src dfs sfs doff soff. alloc_run fresh_outputs
    (compile_struct_typed_copy ce dst src dfs sfs doff soff)
    (\u s. fresh_outputs s))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >>
  conj_tac >- suspend "dispatch" >>
  conj_tac >- (simp[Once compile_store_memory_typed_def] >>
    simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  conj_tac >- (simp[Once compile_store_memory_typed_def] >>
    simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  conj_tac >- suspend "fields" >>
  conj_tac >- suspend "sarray" >>
  conj_tac >- suspend "dynarray" >>
  conj_tac >- (simp[Once compile_store_memory_typed_def] >>
    simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  suspend "struct"
QED

Resume alloc_run_typed_copy[dispatch]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def] >>
  IF_CASES_TAC
  >- (irule alloc_run_bind >> qexists `\u s. fresh_outputs s` >>
      simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
           SRULE [SF ETA_ss] alloc_run_emit_void_fresh]) >>
  IF_CASES_TAC >- simp[alloc_run_compile_store_bytestring] >>
  IF_CASES_TAC >- simp[alloc_run_emit_void_fresh] >>
  Cases_on `dt` >> Cases_on `st` >>
  gvs[alloc_run_compile_copy_memory] >>
  FIRST [first_assum irule >> NO_TAC,
    (rename1 `ArrayT elem dl` >> Cases_on `dl` >>
     qmatch_goalsub_rename_tac `case sl of Fixed _ => _ | Dynamic _ => _` >>
     Cases_on `sl` >> gvs[alloc_run_compile_copy_memory]) >> NO_TAC]
QED

Resume alloc_run_typed_copy[fields]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def, comp_ignore_bind_def] >>
  ntac 3 (irule alloc_run_bind >> qexists `\u s. fresh_outputs s` >>
    reverse conj_tac
    >- (fs[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_compile_with_byte_offset] >>
      first_assum irule) >>
    gen_tac >> simp[comp_ignore_bind_def]) >>
  fs[SF ETA_ss]
QED

Resume alloc_run_typed_copy[sarray]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def] >>
  IF_CASES_TAC >- simp[alloc_run_compile_copy_memory] >>
  gvs[] >> simp[comp_ignore_bind_def] >>
  ntac 3 (irule alloc_run_bind >> qexists `\u s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_fresh_label_fresh] >>
    gen_tac >> simp[]) >>
  irule alloc_run_bind >>
  qexists `\x s. fresh_outputs s /\ not_fresh_at s x /\ ~alloc_owned s x` >>
  reverse conj_tac >- simp[SF ETA_ss, alloc_run_fresh_var_fresh] >>
  qx_gen_tac `counter` >> simp[comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >>
    qexists `\u s. fresh_outputs s /\ not_fresh_at s counter /\ ~alloc_owned s counter` >>
    reverse conj_tac
    >- FIRST [simp[alloc_run_assign_reserved] >> NO_TAC,
        ho_match_mp_tac alloc_run_frame_reserved >>
        fs[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
          SRULE [SF ETA_ss] alloc_run_emit_empty_fresh,
          SRULE [SF ETA_ss] alloc_run_new_block_fresh] >>
        first_assum irule] >>
    gen_tac >> simp[comp_ignore_bind_def]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Resume alloc_run_typed_copy[dynarray]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def, comp_ignore_bind_def] >>
  ntac 7 (irule alloc_run_bind >> qexists `\u s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
    gen_tac >> simp[comp_ignore_bind_def]) >>
  IF_CASES_TAC
  >- (irule alloc_run_bind >> qexists `\u s. fresh_outputs s` >>
      simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
        SRULE [SF ETA_ss] alloc_run_compile_copy_memory_dynamic]) >>
  gvs[] >> simp[comp_ignore_bind_def] >>
  ntac 3 (irule alloc_run_bind >> qexists `\u s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_fresh_label_fresh] >>
    gen_tac >> simp[]) >>
  irule alloc_run_bind >>
  qexists `\x s. fresh_outputs s /\ not_fresh_at s x /\ ~alloc_owned s x` >>
  reverse conj_tac >- simp[SF ETA_ss, alloc_run_fresh_var_fresh] >>
  qx_gen_tac `counter` >> simp[comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >>
    qexists `\u s. fresh_outputs s /\ not_fresh_at s counter /\ ~alloc_owned s counter` >>
    reverse conj_tac
    >- FIRST [simp[alloc_run_assign_reserved] >> NO_TAC,
        ho_match_mp_tac alloc_run_frame_reserved >>
        fs[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
          SRULE [SF ETA_ss] alloc_run_emit_empty_fresh,
          SRULE [SF ETA_ss] alloc_run_new_block_fresh] >>
        first_assum irule] >>
    gen_tac >> simp[comp_ignore_bind_def]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Resume alloc_run_typed_copy[struct]:
  rpt gen_tac >> strip_tac >>
  Cases_on `ALOOKUP sfs name`
  >- suspend "struct_copy" >>
  rename1 `ALOOKUP sfs name = SOME pairval` >>
  Cases_on `pairval` >> suspend "struct_copy"
QED

Resume alloc_run_typed_copy[struct_copy]:
  markerLib.RESUME_TAC >> rpt strip_tac >> gvs[] >>
  simp[Once compile_store_memory_typed_def, comp_ignore_bind_def] >>
  ntac 3 (irule alloc_run_bind >> qexists `\u s. fresh_outputs s` >>
    reverse conj_tac
    >- (fs[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_compile_with_byte_offset] >>
      first_assum irule) >>
    gen_tac >> simp[comp_ignore_bind_def]) >>
  fs[SF ETA_ss]
QED
Finalise alloc_run_typed_copy

Theorem alloc_run_compile_store_memory_typed:
  alloc_run fresh_outputs (compile_store_memory_typed ce dst dt src st)
    (\u s. fresh_outputs s)
Proof simp[alloc_run_typed_copy]
QED

Theorem alloc_run_compile_typed_copy_fields:
  alloc_run fresh_outputs (compile_typed_copy_fields ce dst src dts sts doff soff)
    (\u s. fresh_outputs s)
Proof simp[alloc_run_typed_copy]
QED

Theorem alloc_run_compile_copy_sarray_typed:
  alloc_run fresh_outputs (compile_copy_sarray_typed ce dst dt src st n)
    (\u s. fresh_outputs s)
Proof simp[alloc_run_typed_copy]
QED

Theorem alloc_run_compile_copy_dynarray_typed:
  alloc_run fresh_outputs (compile_copy_dynarray_typed ce dst dt cap src st)
    (\u s. fresh_outputs s)
Proof simp[alloc_run_typed_copy]
QED

Theorem alloc_run_compile_struct_typed_copy:
  alloc_run fresh_outputs (compile_struct_typed_copy ce dst src dfs sfs doff soff)
    (\u s. fresh_outputs s)
Proof simp[alloc_run_typed_copy]
QED
