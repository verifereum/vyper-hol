Theory calldataSelectorProps
Ancestors
  vyperCalldata selectorCompilerProps entryDispatchProps list words

Theorem cd_selector_method_id:
  4 <= LENGTH cd ==> cd_selector cd = w2n (calldata_method_id cd)
Proof
  strip_tac >>
  `LENGTH (TAKE 4 cd) = 4` by simp[LENGTH_TAKE] >>
  drule selectorCompilerPropsTheory.calldata_method_id_four_bytes >>
  simp[GSYM cd_selector_def] >> strip_tac >>
  `calldata_method_id (TAKE 4 cd ++ DROP 4 cd) =
   calldata_method_id (TAKE 4 cd)` by
    (irule calldata_method_id_append >> simp[]) >> gvs[]
QED
