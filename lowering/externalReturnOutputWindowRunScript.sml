Theory externalReturnOutputWindowRun
Ancestors
  externalReturnEncoderOutputs externalReturnEncoderSites externalReturnOutputAlloc
  externalReturnFootprint externalReturnWindowDispatch allocaSiteResource abiEncoderProps
  exprLoweringProps loweringPosts compileEnv fragExec venomState venomInst
  venomMemDefs valueEncoding words finite_map pred_set

Theorem return_output_window_run:
  compile_abi_encode_to_buf dst src ei mid = (out,en) /\
  abi_encoder_admissible ei /\
  abi_encoder_window_input ei at av sb cap u.vs_memory /\
  eval_operand src u = SOME (n2w sb) /\
  eval_operand dst u = SOME (n2w d) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at mid x) /\
  fn_has_code mid en func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es u /\ local_ptrs_reserved cenv mid /\
  FLOOKUP u.vs_allocas output_id = SOME (d,msz) /\
  output_id < mid.cs_next_id /\ LENGTH (enc at av) <= msz /\
  (0 < cap ==> venomMemDefs$regions_disjoint (sb,cap) (d,msz)) /\
  (0 < cap ==>
    (?aid b len. aid < mid.cs_next_id /\
      FLOOKUP u.vs_allocas aid = SOME (b,len) /\
      b <= sb /\ sb + cap <= b + len) \/
    (?name b len. local_region cenv es.scopes u name b len /\
      b <= sb /\ sb + cap <= b + len)) /\
  ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
  u.vs_inst_idx = LENGTH mid.cs_current_insts ==>
  ?actual. abi_encoder_window_result ctx func mid en out at av d u actual
Proof
  strip_tac >>
  `alloca_inv u /\ alloca_room ctx func u /\
   local_ptrs_rel func cenv es.scopes u` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  `d + LENGTH (enc at av) <= u.vs_alloca_next` by
    (gvs[alloca_inv_def, alloca_next_valid_def] >>
     first_x_assum drule >> strip_tac >> decide_tac) >>
  irule return_window_run >> goal_assum (drule_at Any) >>
  asm_rewrite_tac[] >>
  qexistsl_tac [`dst`, `ei`, `sb`, `cap`, `src`] >>
  asm_rewrite_tac[] >> reverse conj_tac
  >- (strip_tac >> conj_tac
      >- (qpat_x_assum `0 < cap ==> (?aid b len. _) \/ _` drule >>
          strip_tac
          >- (gvs[alloca_inv_def, alloca_next_valid_def] >>
              first_x_assum drule >> strip_tac >> decide_tac) >>
          drule_all return_local_region_frontier >> decide_tac) >>
      gvs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  `inst.inst_operands = [Lit 32w]` by
    (drule_all return_encoder_alloca_operands >> simp[]) >>
  `inst.inst_id <> output_id` by
    (gvs[frag_ids_def] >> decide_tac) >>
  drule_all return_output_registered_scratch >> strip_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  qpat_x_assum `0 < cap ==> (?aid b len. _) \/ _` drule >>
  strip_tac
  >- (`aid <> inst.inst_id` by (gvs[frag_ids_def] >> decide_tac) >>
      `venomMemDefs$regions_disjoint (b',len) (b,sz)` by
        (irule alloca_site_registered_disjoint >> metis_tac[]) >>
      gvs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  drule_all return_encoder_alloca_local_disjoint >>
  gvs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem return_output_alloc_reserved:
  compile_alloc_buffer msz st = (buf,mid) /\ local_ptrs_reserved cenv st ==>
  local_ptrs_reserved cenv mid
Proof
  strip_tac >> irule local_ptrs_reserved_next_var >>
  goal_assum (drule_at Any) >>
  qspecl_then [`msz`, `st`] mp_tac ci_mono_compile_alloc_buffer >>
  gvs[ci_mono_def]
QED

(* Producer-to-consumer ledger:
   return_output_alloc_window supplies stmt_state_rel, unchanged actual
   window input/src value, dst value, output registration, and conditional
   positive-cap source/output separation. Its preserved registrations retain
   an old registered source owner; local backing transports through the
   state relation. return_output_alloc_reserved supplies reservation at mid.
   ci_mono_compile_alloc_buffer supplies entry-id monotonicity; the literal
   ALLOCA advances its id, so output_id is strictly before encoder entry.
   Operand freshness is retained by counter monotonicity and the buffer's
   reserved Var witness. The caller still supplies encoder admissibility,
   encoded length <= msz, and entry PC/nonhalt: these are not consequences
   of the pure resource runner. Allocation-PC composition and final RETURN
   result projection are deliberately not claimed here.
   Scratch size/output separation use return_encoder_alloca_operands and
   return_output_registered_scratch. Source scratch separation is derived
   from old-owner ids or return_encoder_alloca_local_disjoint, not assumed.
   At cap=0 no source owner, pointer bound or separation is required. *)
