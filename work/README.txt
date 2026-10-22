Supporting finite checkers for the light-source and exact-half APSP results.

Only the positive-result entrypoints, recorded outputs and Python import
dependencies are bundled here. Their original relative paths are retained
so the checked source files stay byte-identical to the research snapshot.
Run python3 scripts/verify.py from the repository root. The dedicated
scripts/verify_structured_sources.py runs these eight checks and compares
their output byte for byte. The two numerical certificates are in outputs/.
The complete asymptotic proof is outputs/exponent-improvement.tex. Finite
checks do not prove it or the external rectangular multiplication theorem.
Exploratory searches, supplied reviews and research history are not bundled.
