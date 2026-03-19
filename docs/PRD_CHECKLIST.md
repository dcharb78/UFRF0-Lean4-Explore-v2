# Process Requirements Document (PRD) Checklist

Before submitting any PR or merging changes, verify the following pipeline requirements are met. This ensures the rigor of the Universal Field Resonance Framework is upheld.

- [ ] **Zero Custom Axioms**: Ensure zero `axiom` declarations exist. All seeds are definitions and proven theorems (Trinity.lean, Structure13.lean). No physical assumptions may be smuggled into the code.
- [ ] **Zero Sorry**: Ensure `sorry` is entirely removed from all proofs. We maintain a zero-tolerance policy for incomplete proofs.
- [ ] **Sound Tactics Only**: `native_decide` is permitted only on decidable Nat/Fin arithmetic. No `unsafe`, `extern`, or `implemented_by`.
- [ ] **Sync Modules**: Drift between the Lean compilation tree and directory contents is prevented by running `scripts/sync_modules.py`. This ensures `UFRF.lean` matches the filesystem (ignoring `.removed` or `.bak` files).
- [ ] **Run Verify Script**: `./scripts/verify.sh` completes successfully. (Checks for sorries and builds the project).
- [ ] **Run Certify Script**: `./scripts/certify.sh` completes successfully. (Deep audits for axioms and `native_decide`).
