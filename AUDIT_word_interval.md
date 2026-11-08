# Arbitrary-function scalar certificate audit (C1.11)

Evidence: E0018, build TO_word-20261105T144229Z_m0550_t001; source audit TO_word-20261105T144229Z_m0559_t001 through m0568_t001. No falsehood is claimed and no new HOL obligation is admitted here.

## Candidate interface (not proved)

The concrete expression below is the operand of word_interval_expr. Even this specialization already needs more than the finite closed-function certificate:

```sml
!D lo ctx PG fn G0 tn0 s0 n G tn t op sm.
  lower_value compile_expr (FST word_interval_start) (BaseT (IntT 256))
    (IfExp (BaseT (IntT 256)) (Name (BaseT BoolT) "b")
      (Literal (BaseT (IntT 256)) (IntL 1))
      (Literal (BaseT (IntT 256)) (IntL 2)))
    (SND word_interval_start) = (op,sm) /\
  fn_has_code (SND word_interval_start) sm fn /\
  fn_inst_ids_distinct fn /\
  s0.vs_current_bb = (SND word_interval_start).cs_current_bb /\
  s0.vs_inst_idx = LENGTH (SND word_interval_start).cs_current_insts /\
  gas_path_ptr D lo ctx fn PG G0 tn0 s0 n G tn (OK t) /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  op_prov G op = NONE
```

A compiler-wide version would replace the fixed environment/start/expression with cenv/sa/e and add an appropriate word-expression premise. Such a version is NOT justified by this audit.

## Dependency table

In bodyPtrWordBuiltinsIntervalDataflowScript.sml:

| Consumer/premise | Finite fact actually used | Arbitrary-function status |
|---|---|---|
| edge_scalar: instruction lookup/get_instruction | nonterm_scalar and terminator_successor classify fetched instruction | Lookup within emitted blocks derivable from fn_has_code_def; final prefix lookup below endpoint derivable using same_block/split interfaces. Not every fetched instruction is within that region. |
| edge_scalar: nonterminator ghost update | instruction_shapes excludes INVOKE; writers restrict %6 outputs to the two branches; branch_fetch identifies literal ASSIGN at index0 | Holds for the generated blocks; missing for unconstrained suffix/other blocks. INVOKE cannot be ruled out globally. |
| edge_scalar: runtime PC update | step_preserves_control_flow (venomInstProps) | Existing general theorem, independent of code generation; derivable from step_inst=OK and nonterminator. |
| edge_scalar: PHI-entry alternative | no_phis, entry_prov identity, terminator_successor | No PHI at the fixed generated join is computable. Identity on EVERY containing-function block is missing. |
| edge_scalar: direct-jump alternative | terminator_successor + jump_scalars | Generated JMPs and JNZ fixed by emitted-block lookup. Arbitrary suffix terminators/ingress to join are unrestricted. |
| edge_scalar: halt/exit alternatives | result constructor distinctions, exit_result_def | Existing general definitions suffice to eliminate these for OK endpoint. |
| edge_scalar: ptr_safe_step | carried by gas_path_ptr_edge, not needed in this finite closure proof | Does not itself impose scalar provenance for all word variables. No path-confinement premise. |
| operand_path_scalar: lower_value equation | operand_endpoint computes Var %6, join @exit_2 index0 | Independently computed; does not depend on fn. |
| operand_path_scalar: initial PC | scalar_initial makes K empty at entry | Independently computed; arbitrary G0 allowed. |
| operand_path_scalar: path | normal_invariant requires closure for EVERY normal edge | Existing theorem, but global closure is the missing premise, not supplied by fn_has_code. |
| operand_path_scalar: final PC/index | path_scalar selects %6 at join | Independent membership computation, but not provenance proof without closure. |

## Exact contract references

- fragExecScript.sml:112-118: fn_has_code fixes every emitted block by lookup equality and only a prefix of the final current block. No condition on unrelated blocks or incoming jumps from them.
- fragExecScript.sml:208-211 fn_has_code_split and :246-250 fn_has_code_mid give containing code for subintervals using cs_extends. They provide no path restriction.
- fragExecScript.sml:231-235 fn_has_code_start provides start prefix; :259-264 fn_has_code_new_block fixes a finished block. :583-590 fn_has_code_same_block gives exact instruction lookup for offsets strictly inside appended instructions. None constrains offsets at/after the final endpoint.
- fragExecScript.sml:280-283 lookup_block_fn_insts only converts lookup/member to global membership, not uniqueness of outputs.
- venomWfScript.sml:513-516 fn_inst_ids_distinct is ALL_DISTINCT on inst_id only. It does not constrain inst_outputs, operand provenance, PHIs, INVOKE, or jumps.
- bodyPtrDefsScript.sml:216-242 expr_sim_ptr fixes ctx/PG/func as judgment parameters but universally quantifies sa/sb/op/runtime/ghost inputs. body_expr_ptr_ok quantifies the frame including func. The only code conditions in expr_sim_ptr are fn_has_code and instruction-ID distinctness, plus frame conditions. It returns existential gas_outcome_ptr, not a confined path or an all-path theorem.
- fragGasPathPtrScript.sml:23-50 permits direct jumps and PHI-entry as separate normal-edge alternatives. :53-63 does not forbid revisits or traversing final suffixes.
- bodyPtrDefsScript.sml:136-140 ptr_val_ok for a word only demands empty operand taint; it does not demand op_prov=NONE. :100-117 ghost_kept preserves not_fresh_at variables and memory taint conditions, not scalarity of the new operand result.

## Adversarial suffix and PHI analysis

At the operand endpoint the final current instructions are empty in this example. Thus fn_has_code permits arbitrary suffix code there. For a larger full-Abs matching interval the generated Abs prefix is fixed, but code after that larger endpoint remains unrestricted. A normal path may first reach the operand endpoint, continue through code and other blocks, assign another output with name %6 under a distinct instruction ID, and jump back to @exit_2 index0. No global output uniqueness follows from the ID condition. A PC-only K that includes %6 at every @exit_2 PC must therefore justify that extra writer too; the finite writers theorem cannot be generalized merely by interval matching.

An unconstrained block could also contain PHIs. Its entry_prov is not generally identity. Covering only direct jumps misses the alternative where entry_prov applies PHIs; covering only PHI-entry misses the direct-jump alternative. Neither local block prefix lookup nor cs_extends constrains arbitrary other blocks. These are interface obstacles, NOT a checked path/frame counterexample: pointer checks, actual runtime control, final full posts and the exclusion of alternative successful witnesses have not been verified for such a suffix.

The operand judgment supplies an existential source-synchronized path with all its full posts. It does not state that its witness stops at the first join occurrence, does not supply scalar provenance for a word result, and does not supply a whole-function writer certificate. Cutting its witness at first arrival does not preserve source synchronization, marks or full posts, so that retired route stays retired.

## Recommendation: no-go for unrestricted all-path synthesis from fn_has_code alone

Do not attempt global compiler certificate synthesis under only the candidate interface. Any proof based on the current finite K would require genuinely new global assumptions: all reachable writers to protected output names are scalar-preserving; all incoming jumps to protected PCs are covered; all PHI/INVOKE transitions preserve the certificate. These are not generated-interval facts and cannot simply be added to the frozen theorem/judgments. A whole compiler analysis of the extracted module would still not cover arbitrary containing func.

Request ancestor strategy review. A viable replacement must exploit existential construction of a safe simulation witness (without backwards transport of arbitrary witness posts), or find a stronger invariant already derivable from the unchanged full frame. It must explain how scalar operands are obtained at that same constructed endpoint for arbitrary func and arbitrary matching sa. The present audit proves neither that such construction is impossible nor that the frozen target is false. No new compiler induction or counterexample search is authorized by this document.
