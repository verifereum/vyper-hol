Theory vyperTestCoverageReport[no_sig_docs]
Libs vyperTestLib

val () = holbuild_extra_deps ["../VYPER_PIN", "vyper-test-exports"];
val () = holbuild_extra_outputs ["vyper-coverage-report.txt"];
val () = write_coverage_report "vyper-coverage-report.txt";
