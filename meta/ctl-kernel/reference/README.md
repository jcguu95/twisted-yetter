# CTL Kernel v0.1.1 reference artifact

This tree is a protocol-review artifact for CTL Kernel v0.1.1.  It is intentionally
small and strict; it is not a production implementation.

Required commands:

```sh
python3 -m py_compile reference/ctl_ref.py
python3 reference/ctl_ref.py generate-vectors vectors
python3 reference/ctl_ref.py check-vectors vectors
python3 reference/ctl_recompute.py vectors
python3 -m unittest discover -s tests
```

The reference validator covers canonical JSON bytes, object CIDs, mandatory
governance profile validation, RoleBinding identity continuity, RoleBinding
fast-forward checks, policy replacement liveness, golden vectors, and basic
`validate_chain` trust-anchor replay checks.

