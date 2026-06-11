# Upstream `dqrat-check` `d60d50e`: proof parsing can spin forever at EOF when a line misses its trailing `0`

## Symptom

If a proof line ends without the required terminating `0`, upstream `d60d50e`
can enter a pure-CPU infinite loop instead of reporting a parse failure. This
is the same divergence summarized in [docs/benchmarks.md](../benchmarks.md).

The minimal reproducer is the same tiny pair stored as
`repros/proof_missing_zero.dqdimacs` and `repros/proof_missing_zero.dqrat`.

## Minimal repro

```bash
cat > /tmp/proof_missing_zero.dqdimacs <<'EOF'
p cnf 1 1
a 1 0
1 0
EOF

printf '1\n' > /tmp/proof_missing_zero.dqrat

timeout 5 /path/to/dqrat-check /tmp/proof_missing_zero.dqdimacs /tmp/proof_missing_zero.dqrat
echo $?
```

Observed on `d60d50e`:

- the process does not terminate within the timeout
- exit status is `124` from `timeout`
- the process burns CPU rather than blocking on I/O

## Root cause

The proof-reading loop expects `numeric_token` to become `0` when extraction
fails at end-of-file, but that assumption is false in this control path.

More precisely:

- the code uses `ifs >> numeric_token`
- when the stream sentry fails while skipping trailing whitespace at EOF,
  extraction stops before `num_get` is called
- because `num_get` is never entered, the C++11 “store `0` on extraction
  failure” behavior does not fire
- `numeric_token` therefore keeps its previous nonzero value
- the surrounding `while (numeric_token != 0)` loop never makes progress

So the hang is not a semantic issue in DQRAT checking; it is an unchecked
stream-failure path in the parser loop.

## Fix pointer

Check stream state after each numeric extraction in the proof and formula read
loops, and treat extraction failure as parse failure instead of reusing the old
token value.

Any of the following styles is sufficient:

- guard the extraction directly with `if (!(ifs >> numeric_token))`
- break on failed extraction and report a missing terminator
- move the loop condition to the extraction step instead of relying on a stale
  local token

## Notes

The verified Lean checker rejects the same file pair with a parse error rather
than hanging; see [docs/benchmarks.md](../benchmarks.md). This report is only
about CLI robustness on malformed input.
